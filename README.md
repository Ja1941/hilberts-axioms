# Hilbert's axioms in Lean

### About Lean theorem prover

Lean theorem prover is a proof assistant developed principally by Leonardo de Moura at Microsoft Research. It provides a language to formalise concepts in mathematics, discuss their properties and prove theorems about them. Lean is able to check the logical validity down to its logical foundation.

Logical foundation of Lean is based on type theory, which works slightly differently from set theory. Every object is associated with a type and functions are mapping from a type to another. More on type theory in Lean can be found in https://leanprover.github.io/theorem_proving_in_lean/.

More information on Lean and its community is in https://leanprover-community.github.io/. You can also join the Zulip chat for Lean community. See https://leanprover-community.github.io/meet.html for more. If you would like to see more undergrad projects on Lean, refer to Xena project led by Professor Kevin Buzzard at Imperial College London on https://xenaproject.wordpress.com/.

### Project outline

This project develops Euclidean geometry from scratch in Lean, from formalising Hilbert's axioms and defining fundamental objects such as points, lines, segments etc., to proving important theorems in Euclidean geometry such as isosceles theorem, congruence by SSS and many other propositions in *Elements*. For reference, you can look at *Geometry: Euclid and Beyond* by Robin Hartshorne and *Elements* (some proofs are actually similar or even the same).

See https://ja1941.github.io/hilberts-axioms/ for some documentations on important theorems and their proofs.

## What to be done

Many propositions in Elements are still not provable and we need additional axioms and theory of area to work out the rest.

0) Playfair axiom
  This axiom asserts, given a line, the existence of the unique parallel line passing through a fixed point. Most results of Book IV involves this axiom.

1) Circle intersection axiom
  This axiom ensures that two circles meet if one of them contains both points inside the other and outside. You can see this axiom showing up from Book I to IV. This axiom also makes ruler and compass construction formalizable. I am struggling to prove that angles are not trisectable. Although it's just an easy result in field theory, this method seems hard to apply here since we don't have coordinates.

2) Theory of area
  We can define an equivalence relation between rectilinear figures, intuitionally, if they have the same area. This is a useful tool dealing with some propositions in Book III.

In addition, we can add more axioms. Though not directly related to Elements, they gradually complete our axiomatic system to our intuition of real plane. For example,

3) Archimedes' axiom
  Similar to Archimedean property, the axiom says given two segments $s_1$ and $s_2$, we can always find a natural number $n$ such that $n$ copies of $s_1$ is greater than $s_2$.

4) Dedekind's axiom
  Suppose points of a line are divided into two nonempty parts $S$ and $T$ such that no points in $S$ lie between points in $T$ and no points in $T$ lie between points in $S$. Then there exists a unique point such that for all $A\in S$, $B\in T$, either $A=P$ or $B=P$ or $P$ is between $A$ and $B$. You may spot its similarity to dedekind cut. Indeed, this axiom "completes" the system such that it is isomorphic to the real plane!

5) We can define segment and angle arithmetic by taking quotient to segment and angle congruence and then define addition and multiplication on the equivalence classes. Similarity as well as many complicated geometry problems in high school competition is then formalizable.

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

