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
  footer-a: [Abdul Haliq Abdul Latiff],
)

// EXPECTED PACE: 1min 30sec per slide

// smallcaps font
#show smallcaps: set text(font: "Latin Modern Roman Caps")

#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

== Outline <touying:hidden>

#components.adaptive-columns(outline(title: none, indent: 1em))

= Introduction

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

// Plonk
#let plonk = $#math.upright("PLONK")$;
// Plonk.Prover
#let plonkprover = [$plonk$.#smallcaps("Prover")];
// Plonk.Verifier
#let plonkverifier = [$plonk$.#smallcaps("Verifier")];
// Plonk.VerifierFast
#let fast = [#smallcaps("Fast")];
#let pverfast = [$plonk$.#verifier#fast];
//R_IVC
#let IVC = $I V C$;
#let rivc = $vec(R)_(IVC)$;

#slide(align: center + horizon)[
  $
    script(
          & grayed(asverifier(vec(q), acc_(i-1), acc_i)) \
      and & pverfast(pi_(i-1), vec(X)_(i-1), rivc)
    )
  $
][
  TODO: PCDL fast (no check) at a high level
]

#pagebreak(weak: true)

// IVC.Verifier
#let ivcver = [#smallcaps("Verifiers")];

#align(center + horizon)[$
  #math.text("Let ") & ivcver(vec(q), acc_(i-1), acc_i, pi_(i-1), vec(X)_(i-1), rivc) \
                     & =
                       grayed(asverifier(vec(q), acc_(i-1), acc_i)) \
                     & grayed(and pverfast(pi_(i-1), vec(X)_(i-1), rivc))
$]

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
        & ivcver^p (vec(q)^((p)), dots, rivc^((p))) \
    and & ivcver^q (vec(q)^((q)), dots, rivc^((q)))
  $
][
  TODO: Cycle of Curves & Pasta Curves at a high level
]

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
        & ((ivcver^p (dots) and ivcver^q (dots)) \
     &or s_(i-1) attach(=, t: ?) s_0) \
    &and F(s_(i-1), s_i)
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
  TODO: Chain of Signatures at a high level (chain / loop diagram)
]

#pagebreak(weak: true)

#figure(
  image("./media/rivc_diagram.png", width: 100%),
)

== Plonk

Plonk is a snark
#align(center)[$
  (vec(x), vec(w)) in R_IVC
$]
where $IVC(vec(w))$ is output of program and $vec(x)$ is public input

TODO (public inputs at a high level)

#pagebreak(weak: true)

#align(center)[$
  P arrow.r.squiggly V & : plonkprover(vec(X), vec(R), vec(W)) &               = & pi \
                     V & : plonkverifier(pi, vec(X), vec(R))   & attach(=, t: ?) & top
$]

#let fgc = $F_(G C)$;

TODO (maybe multi slides here)
- Semantic Polynomials
  - Gate Constraint Polynomial $fgc$
  - Grand Product Argument $product f(X) = product g(X) arrow.r.squiggly F_1, F_2$
- Subprotocols
  - Vanishing Argument (schwartz-zippel lemma) $forall F(X) = 0 and F != 0$
  - Batched Evaluation Proofs

== Motivation

// Arithmetize
#let arith = smallcaps("Arithmetize");
// Arithmetize_pub
#let pub = $p u b$;

#align(center)[$
  P arrow.r.squiggly V & : plonkprover compose arith(vec(w), IVC)            &                = pi \
                     V & : plonkverifier(pi) compose arith_pub (vec(x), IVC) & attach(=, t: ?) top
$]

#pause
#align(center)[#text(size: 0.75em)[#emph[
  1. a program is arithmetizable if it can be decomposed into canonical programs of the scheme
  2. a scheme is viable if the curve can express the total number of constraints
  3. light node is viable if the verifier performance is "acceptable"
]
#pause
#align(left)[
#emph("features") (#strong("C")- correctness, #strong("O")- optimization, #strong("E")- expressivity)]
#table(
  columns: (1fr, 10fr),
  inset: 10pt,
  align: horizon + left,
  [#strong("O,E")],
  [type safe multi in out gates via properads],
  [#strong("O,E")],
  [rewriting of user defined algebraic identities],
  [#strong("E")],
  [elegant handling of transcript hash via index maps],
  [#strong("C,E")],
  [user extensible single source of truth scheme via spec],
  [#strong("C,O")],
  [relative wires; gate declaration invariant]
)
]]




= Arithmetization

== Pipeline

#let interpolate = $text("interpolate")$
#let trace = $text("trace")$;
#let tracepub = $text("trace")_pub$;
#let build = $text("build")$;
#slide(align: center + horizon)[
  $
      & (vec(X), vec(R), vec(W)) \
    = & arith(vec(w), IVC) \
    = & interpolate compose trace compose build
  $
][
  $
      & (vec(X), vec(R)) \
    = & arith_pub (vec(x), IVC) \
    = & interpolate compose tracepub compose build
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
- trace defn of mono compose

#let copym = $text("copy")$;
#let gatem = $text("gate")$;
#let gatempub = $text("gate")_pub$;
#let resolvem = $text("resolve")$;

#table(
  columns: (1fr, 1fr, 1fr, 1fr),
  inset: 10pt,
  align: horizon + center,
  table.header($copym$, $gatem$, $gatempub$, $resolvem$),
  [a],
  [b],
  [c],
  [d]
)


== Interpolate

TODO
- root of unity and cosets
- fast fourier interpolation

== Example

TODO: tie to motivation in overview
- poseidon gate
- message passing gate & public input gate

= Conclusion

== Summary

TODO
- IVC for light node catchup
- informs arithmetization demands
- benefits of formalization
- general scheme extending beyond thesis use case and even plonk

== Future Work

TODO
- full specification (copy, interpolate, prover, verifier); agda? hacspec?
- properad and relative gate compute caching
- user domain specific algebraic optimization via egglog rewriting
- dependent properads (e.g.table row count dependent properads); root of unity, optimal multi lookup (dynamic mina lookups)
- full correctness and soundness proofs of arith
