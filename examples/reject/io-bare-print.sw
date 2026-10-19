-- expect-error: E-UNKNOWN-NAME
-- `print` is not a default name: write `IO.print`, or `import IO (print)`.
def main(): {IO} () := print "hi"
