# Hilbert's axioms in Lean

### About Lean theorem prover

Lean theorem prover is a proof assistant developed principally by Leonardo de Moura at Microsoft Research. It provides a language to formalise concepts in mathematics, discuss their properties and prove theorems about them. Lean is able to check the logical validity down to its logical foundation.

Logical foundation of Lean is based on type theory, which works slightly differently from set theory. Every object is associated with a type and functions are mapping from a type to another. More on type theory in Lean can be found in https://leanprover.github.io/theorem_proving_in_lean/.

More information on Lean and its community is in https://leanprover-community.github.io/. You can also join the Zulip chat for Lean community. See https://leanprover-community.github.io/meet.html for more. If you would like to see more undergrad projects on Lean, refer to Xena project led by Professor Kevin Buzzard at Imperial College London on https://xenaproject.wordpress.com/.

### Project outline

This project develops Euclidean geometry from scratch in Lean, from formalising Hilbert's axioms and defining fundamental objects such as points, lines, segments etc., to proving important theorems in Euclidean geometry such as isosceles theorem, congruence by SSS and many other propositions in *Elements*. For reference, you can look at *Geometry: Euclid and Beyond* by Robin Hartshorne and *Elements* (some proofs are actually similar or even the same).

See https://ja1941.github.io/hilberts-axioms/ for some documentations on important theorems and their proofs.

### How to run the project

0) Install lean and git. More information can be found on https://leanprover-community.github.io/get_started.html. If you can run

`$ git --version`

and 

`$ lean --version`

on your command line and get no errors, you are probably fine to move forward.

1) Clone the repo:

`$ git clone https://github.com/Ja1941/Hilberts-axioms.git`

2) Install the dependencies (currently mathlib; in the future there will be a xena repository containing more mathematics):

```
$ cd Hilberts-axioms
$ leanpkg configure
```

3) (optional, will take a while and will use a lot of power, but will make mathlib run *much* faster): build mathlib.

```
$ cd _target/deps/mathlib/
$ leanpkg build
```

