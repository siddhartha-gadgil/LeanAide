# ATP-Project
Notes etc for the ATP project

## Checking and Comparing theorems as strings

The `lean` utility `chkthms` can check if strings can be parsed (and elaborated) in `lean`, and also check if two such strings give  _definitionally equal_ terms. 

The strings are passed as arguments, with the task depending on the number of arguments. First, some examples, starting with building the script.

```bash
$ lake build

$ build/bin/chkthms "theorem nonsense(n : Nat) (m : Nat) : n = m" 
success
forall (n : Nat) (m : Nat), Eq.{?_uniq.7} Nat n m

$ build/bin/chkthms "theorem nonsense(n : Nat) (m : Nat) : n = m" "(p : Nat)(q: Nat) : p = q"
success
true

$ build/bin/chkthms "theorem nonsense(n : Nat) (m : Nat) : n = m" "(p : Nat)(q: Nat) : p = q + 1"
success
false
```

More detailed instructions are below, and call also be obtained by running the script with no arguments.

### Detailed instructions

`chkthms` is a utility to check whether a theorem string can be parsed (and elaborated) in lean.

- Give a single argument to check parsing.
- Give two arguments to compare results (if parsing is successful).

A theorem can be given in one of two forms

- the word `theorem` followed by a name, then the arguments, a `:`, finally the statement, or
- the arguments, a `:`, and the statement. 

The following examples are of these two forms:

- `theorem nonsense(n : Nat) (m : Nat) : n = m` 
- `(p : Nat)(q: Nat) : p = q`

Note that the arguments can be implicit or explicit. 

The underlying code also supports `open` for namespaces but this demo version does not use these. 