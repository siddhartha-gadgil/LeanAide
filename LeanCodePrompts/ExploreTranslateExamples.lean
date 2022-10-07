import LeanCodePrompts.ExploreTranslate
import Mathbin.All

def eg1 := "There are infinitely many odd numbers."

#eval translate eg1

def eg2 := "Every set of `10` distinct numbers between `1` and `100` contains two disjoint nonempty subsets with the same sum."

#eval translate eg2

def eg3 := "If a set `S` contains `0` and `1`, and the mean of every finite nonempty subset of `S`, then `S` contains all the rational numbers in the unit interval."

#eval translate eg3 #[("`3` is odd", ": Odd 3")]

#eval showLogs 1

def eg4 := "Every sequence of natural numbers is bounded."

#eval translate eg4

def eg5 := "Every sequence `x_n` of natural numbers is constant."

#eval translate eg5

def eg6 := "Every finite sequence `x_1, x_2, ..., x_n` of natural numbers is bounded."

#eval translate eg6

#eval showLogs 1

def eg7 := "If a set `S` contains `0` and `1`, and the mean of every finite nonempty subset of `S`, then `S` is non-empty."

#eval translate eg7

#eval showLogs 1