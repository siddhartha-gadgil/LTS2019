task default: %w[build]
$linebreak = "\n\n =========================\n"

task :build do
  clean
  puts $linebreak
  puts "Building for production"
  jekyll "build"
end

task :test do
  
end

def jekyll(args)
  system "jekyll #{args}"
end

def clean
  puts $linebreak
  puts "Cleaning previous builds"
  system "rm -Rf _site/"
end
