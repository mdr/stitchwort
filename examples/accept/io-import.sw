-- `import IO (...)` brings an ability's operations in by their short names.
import IO (print, readLine)

def main(): {IO} () :=
  let l := readLine()
  print "hi"
