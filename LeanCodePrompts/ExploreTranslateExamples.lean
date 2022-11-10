import LeanCodePrompts.ExploreTranslate
import Mathbin.All

/-
def eg1 := "There are infinitely many odd numbers."

#eval translate eg1

#eval showLogs 1

def eg2 := "Every set of `10` distinct numbers between `1` and `100` contains two disjoint nonempty subsets with the same sum."

#eval translate eg2

def eg3 := "If a set `S` contains `0` and `1`, and the mean of every finite nonempty subset of `S`, then `S` contains all the rational numbers in the unit interval."

#eval translate eg3 

#eval showLogs 1

def eg4 := "Every sequence of natural numbers is bounded."

#eval translate eg4

def eg5 := "Every sequence `x_n` of natural numbers is constant."

#eval translate eg5

def eg6 := "Every finite sequence `x_1, x_2, ..., x_n` of natural numbers is bounded."

#eval translate eg6

#eval showLogs 1

def eg7 := "If a set of natural numbers `S` contains `0` and `1`, and the mean of every finite nonempty subset of `S`, then `S` is non-empty."

#eval translate eg7

-- #eval showLogs 1

#eval dotName? "S.nonempty"

def eg8 := "Every complete pseudometric space is a Baire space."

#eval translate eg8

-/

def eg9 := "If $n$ is a prime number, then $$\\Phi_n(x) = 1+x+x^2+\\cdots+x^{n-1}=\\sum_{k=0}^{n-1}x^k$$, where $\\Phi_n$ is the $n$-th cyclotomic polynomial."

-- Formula translation incorrectly, must try with partial translation to Lean + Unicode
#eval translate eg9

def eg10 := "The Möbius inversion formula allows the expression of the $n$-th cyclotomic polynomial $\\Phi_n(x)$ as an explicit rational fraction $$\\Phi_n(x)=\\prod_{d\\mid n}(x^d-1)^{\\mu \\left(\\frac{n}{d} \\right)$$, where $\\mu$ is the Möbius function."

-- not working for some reason
-- #eval translate eg10

def eg11 := "The function `ψ : ℝ → ℝ` that takes the value $\\exp((-1)/(1 - x^2))$ on $(-1, 1)$ and $0$ everywhere else is smooth and compactly supported."

#eval translate eg11

-- this example is in `mathlib`
def eg12 := "If `f : ℂ → E` is continuous on a closed disc of radius $R$ and is complex differentiable at all but countably many points of its interior, then the integral $\\oint_{|z-c|=R} \\frac{f(z)}{z-c}\\,dz$ is equal to $2πiy$."

#eval translate eg12

-- Initial translation failed to recognise `tangent function` as a synonym/expansion of `tan`. Adding `tan` explicitly seems to have fixed this
def eg13 := "The tangent function `tan` is periodic with period `π`."

#eval translate eg13

#eval showLogs 1

-- this workss
-- def eg14 := "The function `exp(-x)` tends to `0` as `x` tends to `∞`."

-- #eval translate eg14

-- this works
-- def eg15 := "Every finite field has non-zero characteristic."

-- #eval translate eg15

def eg16 := "Functors between categories preserve composition of morphisms."

#eval translate eg16

def eg17 := "If a function $f:\\mathbb{C} \to \\mathbb C}$ is entire and non-constant, then the set of values that $f(z)$ assumes is either the whole complex plane or the plane minus a single point."

#eval translate eg17