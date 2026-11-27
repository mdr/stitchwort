namespace Probe.Run

import Probe.Fn (Stream)

def main(): {IO} () := IO.print "${((Stream.iterate (+ 1) 0).take 2000).sum}"
