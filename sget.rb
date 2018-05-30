#!/usr/bin/ruby

require "uri"
require "json"
require "yaml"
require "digest"
require "fileutils"
require "optparse"
require "http"
require "nokogiri"
require "trollop"

SGET_DEFAULTS = {
  useragent: "Mozilla/5.0 (Windows NT 6.3; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/53.0.2785.80 Safari/537.36",
}

module Utils
  def self.mkclean(olds)
    s = olds.scrub.gsub(/[^[:ascii:]]/, "").gsub(/[^[:alnum:].-]/, "-")
    %w(- _ .).each do |c|
      dup = Regexp.new(Regexp.quote(c) + "{2,}")
      while (w=s.match(dup)) != nil do
        s.gsub!(dup, c)
      end
    end
    s.gsub!(/^[-_.]/, "")
    return s
  end

  def self.mkname(url, selextension=nil)
    # get url components (for query string)
    purl = URI.parse(url)
    extension = File.extname(purl.path)
    basename = File.basename(purl.path, extension)
    # make a "clean" name ...
    #cleanname = (basename + (purl.query ? purl.query : "")).gsub(/[^0-9A-Za-z]/, "-").gsub(/^-/, "")
    cleanname = mkclean(basename + (purl.query ? purl.query : ""))
    # if filename exceeds a certain length, turn it into a hash sum instead
    # (rather than trying to figure out how to create a unique filename, even by shrinking ...)
    # appends the first 10 characters from the original cleanname, to ease identification
    if cleanname.length > 500 then
      #mlog("filename is too long, using hashsum instead")
      #cleanname = cleanname[0 .. 10] + Digest::MD5.hexdigest(cleanname)
      hexdg = Digest::MD5.hexdigest(cleanname)
      cleanname = sprintf("%s-%s", cleanname[0 .. 20], hexdg[0 .. 8])
    end
    # create a physical location for the file to be written to
    if (selextension == nil) || (extension.length == 0) || (extension == "") then
      extension = "unknown"
    end
    if (extension.length > 0) && (extension[0] == ".") then
      extension = extension[1 .. -1]
    end
    return (cleanname + "." + extension)
  end
end

class HTTPClient
  attr_accessor :response

  def initialize(url, params={}, method: "get", follow: true, timeout: 5, headers: {})
    #HTTP.get(url, params: params).follow()
    #@response = HTTP.send(method)
    @response = HTTP.timeout(:global,
      :write => timeout,
      :connect => timeout,
      :read => timeout
    ).headers(headers).follow(follow).send(method, url)

  end

  def _verify
    stcode = @response.code
    if stcode != 200 then
      raise "HTTP status error (expected 200, got #{stcode})"
    end
  end

  def body
    return @response.body
  end

  def code
    return @response.code
  end

  def ok?
    return (@response.code == 200)
  end

  def failed?
    return (ok? == false)
  end

  def to_file(path)
    _verify
    dirp = File.dirname(path)
    FileUtils.mkdir_p(dirp) unless File.directory?(dirp)
    File.open(path, "wb") do |fh|
      # a neat feature of http.rb is that it only retrieves
      # the header at first -- which makes HTTP queries very lightweight.
      # the actual body is downloaded later (http.rb calls it streaming),
      # and here's a prime example of how useful this actually is!
      while true do
        data = @response.readpartial
        break if (data == nil)
        fh.write(data)
      end
    end
  end
end

class Selector
  attr_accessor :selector, :node, :extension, :post

  def initialize(expr, rnode, extension="file", post=nil)
    @selector = expr
    @node = rnode
    @extension = extension
    @post = post
  end
end

class SiteGet
  # most of these are *static* attempts at figuring out where resources are.
  # ideally, this should be done dynamically; i.e., checking response headers, and
  # even having to partially interpret javascript, especially since things like coffeescript
  # imply that a resource that looks like garbage could end up being code that gets preprocessed...
  # same thing goes for SVG, et al. so this is as good as it gets.
  # sorry :-(
  @@selectors =
  [
    # javascript
    {sel: "script[src]", rep: "src", ext: "js", post: nil}, #JSPostProcessor
    # fucking twitter
    {sel: "link[href][as=script]", rep: "href", ext: "js", post: nil},

    # images
    {sel: "img", rep: "src", ext: nil},
    {sel: "image", rep: "src", ext: nil},
    {sel: "img[data-thumb]", rep: "data-thumb", ext: nil, post: nil},
    {sel: "img[data-src]", rep: "data-src", ext: nil, post: nil},
    {sel: "input[src][type=image]", rep: "src", ext: nil, post: nil},
    # css
    {sel: "link[rel=stylesheet][href]", rep: "href", ext: "css", post: nil}, # CSSPostProcessor
    # favicons
    {sel: "link[rel*=icon][href]", rep: "href", ext: nil, post: nil},
    {sel: "link[rel*=shortcut][href]", rep: "href", ext: nil, post: nil},
  ]


  def initialize(uri, opts)
    $stdout.sync = false
    @opts = opts
    @site = geturl(uri.to_s)
    @parsed = uri
    @flog = {info: {}, urls: []}
    FileUtils.mkdir_p(@opts.destination)
  end

  def mlog(fmt, *args)
    #$stdout << "-- " << str << "\n"
    $stderr.printf("-- %s\n", sprintf(fmt, *args))
  end


  def writelog
    File.open(File.join(@opts.destination, "url-log.json"), "wb") do |fh|
      fh.write(JSON.pretty_generate(@flog))
    end
  end

  def geturl(url, **kwargs)
    mlog("downloading %p ...", url)
    #res = HTTP.follow(true).get(url)
    res = HTTPClient.new(url, headers: {"User-Agent" => @opts.useragent})
    if res.failed? then
      mlog("failed? HTTP code=%d", res.code)
      return nil
    end
    return res
  end



  # this monstrosity of a function parses and (re)creates URLs, based on whether
  # they are relative, absolute, or remote.
  # input is the URL, and the selector hash, returns the generated local destination.
  # will download the file is the local destination does not exist yet.
  def mkurl(oldurl, selector)
    mlog("checking %p ...", oldurl)
    url = oldurl
    # yes, technically one can include a resource from FTP.
    # some people actually do that.
    # but you really shouldn't.
    if oldurl.match(/^(https?|ftp)/) or (autoscm = oldurl.match(/^\/\//)) then
      if autoscm then
        # in case of "//somehost.com/..." urls, just create an absolute url by
        # reusing the scheme from the mothership
        url = @parsed.scheme + ":" + oldurl
      end
    else
      # macgyver the url together from the mothership scheme and host
      url = String.new
      url << @parsed.scheme << "://" << @parsed.host
      # if the url starts with a slash, it's an absolute path (i.e., "/blah/something.js")
      if oldurl.match(/^\//) then
        url << oldurl
      else
        # otherwise, it's a relative one (i.e., "subdir/whatever/thing.js")
        url << File.dirname(@parsed.path)
        if ((url[-1] != "/") && (oldurl[0] != "/")) then
          url << "/"
        end
        url << oldurl
      end
    end
    localdest = File.join(@opts.resdir, Utils.mkname(url, selector))
    fulldest = File.join(@opts.destination, localdest)
    # coincidentally, the local url is the same as the file dest. whudathunkit
    @flog[:urls] << {url: url, local: fulldest}
    if File.file?(fulldest) then
      return localdest
    end
    response = geturl(url)
    if response then
      mlog("storing as %p", fulldest)
      FileUtils.mkdir_p(File.join(@opts.destination, @opts.resdir))
      response.to_file(fulldest)
      return localdest
    end
    raise Exception, "bad response from geturl?"
  end

  def parse
    removeme = %w(crossorigin integrity)
    @flog[:info][:mainpage] = @parsed.to_s
    body = @site.body.to_s
    main = Nokogiri::HTML(body)
    @@selectors.each do |selector|
      # iterate over each selector
      mlog("++ processing selector %p ...", selector[:sel])
      if (nodes = main.css(selector[:sel])) then
        nodes.each do |node|
          removeme.each do |rm|
            node.remove_attribute(rm)
          end
          url = node[selector[:rep]]
          if url != nil then
            localurl = mkurl(url, selector)
            mlog("rewriting %p", url)
            # modify the node with the new url
            # gotta love nokogiri
            node[selector[:rep]] = localurl
          end
        end
      end
    end
    # write the shite to file
    File.open(File.join(@opts.destination, @opts.htmlfile), "w") do |fh|
      fh << main.to_html
    end
  end
end

begin
  #opts = Trollop::options do
  #  opt :destination, "Use <destination> as directory to store website", default: ".", type: :string
  #  opt :htmlfile, "Use <htmlfile> instead of index.html", default: "index.html", type: :string
  #  opt :resdir, "Use <resdir> instead of 'res' as resources directory name", default: "res", type: :string
  #end
  opts = OpenStruct.new({
    destination: nil,
    htmlfile: "index.html",
    resdir: "res",
  })
  prs = OptionParser.new{|prs|
    prs.on("-d<s>", "--destination=<s>", "Use <destination> as directory to store website"){|s|
      opts.destination = s
    }
    prs.on("-f<s>", "--htmlfile=<s>", "Use <htmlfile> instead of index.html"){|s|
      opts.htmlfile = s
    }
    prs.on(nil, "--resdir=<s>", "Use <resdir> instead of 'res' as resources directory name"){|s|
      opts.resdir = s
    }
  }
  prs.parse!
  if ARGV.length > 0 then
    arg = ARGV.shift
    uri = URI.parse(arg)
    if opts.destination.nil? then
      opts.destination = uri.host
    end
    sg = SiteGet.new(uri, opts)
    begin
      sg.parse
    ensure
      sg.writelog
    end
  elsif ARGV.length > 1 then
    puts "can only process one URL at a time!"
  else
    puts "usage: sget <URL>"
  end
end
