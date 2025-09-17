#import "@preview/touying:0.6.1": *
#import themes.university: *

#import "@preview/numbly:0.1.0": numbly

#show: university-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Master's Thesis Examination],
    subtitle: [#text(size: 0.8em)[Light Node Catchup Using Incrementally Verifiable Chain of Signatures] \ #emph[#text(
        size: 0.7em,
      )[Focus of presentation: Plonk Arithmetization Formal Specification]]],
    author: [#strong[supervisor]: Diego Aranha, #strong[co-supervisor]: Hamidreza Khoshakhlagh #linebreak() #v(0em) Rasmus Kirk Jakobsen, #underline[Abdul Haliq Abdul Latiff]],
    date: datetime(year: 2025, month: 9, day: 26),
    institution: [Aarhus Universitet],
  ),
)

// EXPECTED PACE: 1min 30sec per slide

// smallcaps font
#show smallcaps: set text(font: "Latin Modern Roman Caps")

#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

== Outline <touying:hidden>

#components.adaptive-columns(outline(title: none, indent: 1em))

= Overview

== Light Node Catchup

// AS.Verifier
#let accscheme = $#math.upright("AS")$;
#let verifier = [#smallcaps("Verifier")];
#let asverifier = [$accscheme$.#verifier];
// bold vector notation
#let vec(x) = $#math.bold(x)$;
// acc
#let acc = $#math.text("acc")$;
// gray out
#let grayed(x) = text(fill: gray, $#x$)

#slide(align: center + horizon)[
  $
    asverifier(vec(q), acc_(i-1), acc_i)
  $
][
  TODO: Accumulation Schemes at a high level (instances and accumulators)
]

#pagebreak(weak: true)

// Plonk.VerifierFast
#let plonk = $#math.upright("PLONK")$;
#let fast = [#smallcaps("Fast")];
#let pverfast = [$plonk$.#verifier#fast];
//R_IVC
#let IVC = $I V C$;
#let rivc = $R_(IVC)$;

#slide(align: center + horizon)[
  $
    script(
          & grayed(asverifier(vec(q), acc_(i-1), acc_i)) \
      and & pverfast(rivc, x_(i-1), pi_(i-1))
    )
  $
][
  TODO: PCDL fast (no check) at a high level
]

#pagebreak(weak: true)

#let ivcver = [$IVC$.#verifier];

#align(center + horizon)[$
  #math.text("Let ") & ivcver(vec(q), acc_(i-1), acc_i, rivc, x_(i-1), pi_(i-1)) \
                     & =
                       asverifier(vec(q), acc_(i-1), acc_i) \
                     & and pverfast(rivc, x_(i-1), pi_(i-1))
$]

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
        & ivcver^p (vec(q)^((p)), dots, rivc^((p)), dots) \
    and & ivcver^q (vec(q)^((q)), dots, rivc^((q)), dots)
  $
][
  TODO: Cycle of Curves & Pasta Curves at a high level
]

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
        & (... \
     or & s_(i-1) attach(=, t: ?) s_0) \
    and & F(s_(i-1), s_i)
  $
][
  TODO: IVC at a high level (where s comes from)
]

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
    F = ...
  $
][
  TODO: Chain of Signatures at a high level
]

#pagebreak(weak: true)

$IVC = ...$

TODO kirk's diagram from thesis

TODO IVC chain / loop diagram

== Plonk Language

Plonk is a snark
#align(center)[$
  (vec(x), vec(w)) in R_IVC
$]
where $IVC(vec(w))$ is output of program and $vec(x)$ is public input

TODO (message passing at a high level and where it is used)

== Plonk Protocol

#let plonkprover = [$plonk$.#smallcaps("Prover")];
#let plonkverifier = [$plonk$.#smallcaps("Verifier")];
#align(center)[$
  P arrow.r.squiggly V & : plonkprover(vec(X), vec(R), vec(W)) &               = & pi \
                     V & : plonkverifier(pi, vec(X), vec(R))   & attach(=, t: ?) & top
$]

TODO
- Grand Product Argument
  - $f,g mapsto (F_1, F_2)$
- Vanishing Argument
  - schwartz-zippel lemma
- Batched Evaluation Proofs
  - $F_(G C)$, $F_(C C 1)$, $F_(C C 2)$, and possibly $F_(P L 1)$, $F_(P L 2)$
  - example F_GC?

== Motivation

#let arith = smallcaps("Arithmetize");
#let pub = $p u b$;
#align(center)[$
  P arrow.r.squiggly V & : plonkprover compose arith(vec(w), IVC)            &                = pi \
                     V & : plonkverifier(pi) compose arith_pub (vec(x), IVC) & attach(=, t: ?) top
$]

#align(center)[#text(size: 0.8em)[#emph[
1. a program is arithmetizable if it can be decomposed into canonical programs of the scheme
2. a scheme is viable if the curve can express the total number of constraints
3. light node is viable if the verifier performance is "acceptable"
]]]

TODO
- multi in out gates (turbo plonk) & type safe (halo) via properads
- constraint reduction via relative wires; gate order invariant
- possible constraint reduction via rewriting of algebraic identities
- elegant handling of transcript hash via index maps
- user extensible single source of truth scheme via spec

= Plonk Arithmetization

== Pipeline

#slide(align: center + horizon)[
  $
      & (vec(X), vec(R), vec(W)) \
    = & arith(vec(w), IVC) = ...
  $
  TODO
][
  $
      & (vec(X), vec(R)) \
    = & arith_pub (vec(x), IVC) = ...
  $
]

== Build

TODO
- spec abstractions table; constraint, gate, properads
- build predicate
- example proof and abstract circuit diagram

== Abstractions

TODO
- index maps & equations
  - F_GC (emphasis ease of use in arith, prover and verifier)

== Trace

TODO
- monotone functions
- resolve, gate, copy; and public variants

== Interpolate

TODO
- root of unity and cosets
- fast fourier interpolation

== Example

TODO
- poseidon gate
- message passing gate & public input gate

= Conclusion

== Conclusion

TODO
- IVC for light node catchup
- informs arithmetization demands
- benefits of formalization
- general scheme extending beyond thesis use case and even plonk

== Future Work

TODO
- full specification (copy, interpolate, prover, verifier); agda? hacspec?
- properad and relative gate compute caching
- egglog rewriting
- dependent properads (e.g.table row count dependent properads); root of unity, optimal multi lookup (dynamic mina lookups)
- full correctness and soundness proofs of arith
