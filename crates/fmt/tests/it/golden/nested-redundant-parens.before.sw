-- D2307: nested redundant pairs after an ability row all go in one pass.
def main(): {IO} ( (halvings 100 0))
def withBody(): {IO} ( (halvings 100 0)) := halvings 100 0
def three(): {IO} (((halvings 100 0)))
def threeWithBody(): {IO} (((halvings 100 0))) := halvings 100 0
