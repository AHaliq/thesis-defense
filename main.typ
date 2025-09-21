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
#let prover = [#smallcaps("Prover")];
#let asverifier = [$accscheme$.#verifier];
#let asprover = [$accscheme$.#prover];
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
  #v(1em)
  #box(
    stroke: black,
    inset: 1em,
    $
      script((q_i, acc_i) #h(0.5em) attach(stretch(->), t: \_ #h(0.5em) dot.circle asprover) #h(0.5em) (q_(i+1), acc_(i+1))) \
      sscript(Phi(q_i) = top)
    $,
  )
][
  "Compresses" instances $vec(q)$ into a proof that they satisfy a predicate $Phi$ as an accumulator. Verifier checks it comes from previous accumulator. Decider checks $Phi$ holds.

  #emph([Think: $vec(q)$ are plonk proofs; $Phi$ plonk verification holds. $asverifier$ checks accumulator integrity.])
]

// Protocols (Accumulation Scheme):
// - AS.Prover: Compresses instances and previous accumulator into a new accumulator
// - AS.Verifier: Verifies new accumulator is legitimate
// - AS.Decider: Single check that all instances in the accumulator satisfies the predicate
// Soundness: Decider AND Verifier implies w.n.p. that the predicate holds for all instances.

#pagebreak(weak: true)

// Plonk
#let plonk = $#math.upright("PLONK")$;
// Plonk.Prover
#let plonkprover = [$plonk$.#prover];
// Plonk.Verifier
#let plonkverifier = [$plonk$.#verifier];
// Plonk.VerifierFast
#let fast = [#smallcaps("Fast")];
#let pverfast = [$plonk$.#verifier#fast];
//R_IVC
#let IVC = $I V C$;
#let rivc = $vec(R)_(IVC)$;
// IVC.Verifier
#let ivcver = [#smallcaps("Verifiers")];

#slide(align: center + horizon)[
  $
    script(
      #math.text("Let ") & ivcver(...) \
                       = & grayed(asverifier(vec(q), acc_(i-1), acc_i)) \
                     and & pverfast(pi_(i-1), vec(X)_(i-1), vec(R))
    )
  $
  #v(1em)
  #box(
    stroke: black,
    inset: 1em,
    $
      script((pi_i, acc_i) #h(0.5em) attach(stretch(->), t: plonkprover) #h(0.5em) (pi_(i+1), acc_(i+1))) \
      sscript(Phi(pi_i) = plonkverifier(pi_i, vec(X)_i, vec(R)) attach(=, t: ?) top)
    $,
  )
][
  Plonk uses polynomial commitment schemes, thus the verifier checks commitments. However we can offload this to the accumulation scheme. Without the check it is fast; sub-linear.

  #emph([Think: $pi$ is an instance; $vec(q)$. And $vec(X)$ is composed of the accumulator.])
]

// Protocols (Polynomial Commitment Scheme) constructed in terms of bulletproofs
// - PCDl.Commit: commits polynomial
// - PCDl.Open: creates a proof of evaluation
// - PCDl.Check: verifies proof of evaluation
// - Knowledge Soundness: If an adversary creates a valid instance, there exists a knowledge extractor that can recover the polynomial used failing w.n.p.
// - Binding: Polynomial sized adversaries can change the committed polynomial w.n.p.
//
// Protocols (Bulletproofs) constructed in terms of pedersen commitments
// - is an inner product argument:
// - given $vec(b), vec(c)$ and commitment of $vec(a)$, proves $vec(c) = vec(a) dot.circle vec(b)$
// - reduction proof
//
// Protocols (Pedersen Commitments)
// - homomorphic over addition

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
        & ivcver (vec(q)^((p)), dots, rivc^((p))) \
    and & ivcver (vec(q)^((q)), dots, rivc^((q)))
  $
  #box(stroke: black, inset: 1em, [
    #emph([More on this in message passing])])
][
  Computing commits uses scalar multiplication; $m G$, thus two fields; scalar $m: FF_cal(S)$ and base $G: EE(FF_cal(B))$. Pasta curves is a two cycle of curves where the scalar field of the other is its base field. This can express $m G$ in IVC.

  #emph(
    [Think: A circuit has multiple types. If a circuit of $f$ has canonical type $t$, then $f^((p))$ sets $t = p$ and $t'=q$],
  )
]

// - natively handled in the base field circuit
// - i.e. a circuit has one table per field
// Foreign field uses a single smaller field, with larger field modulo gadget. This is expensive.

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
    IVC(...) = \
    ((ivcver^p (dots) and ivcver^q (dots)) \
      or s_(i-1) attach(=, t: ?) s_0)
    and F(s_(i-1), s_i)
  $
  #v(1em)
  #box(stroke: black, inset: 1em, [
    $
      script((s_i, pi_i, acc_i) #h(0.5em) attach(stretch(->), t: cal(P)) #h(0.5em) (s_(i+1),pi_(i+1), acc_(i+1)))
    $
    $
      sscript(
        Phi(pi_i) & = forall t. plonkverifier^t (pi_i^((t)), vec(X)_i^((t)), rivc^((t))) attach(=, t: ?) top \
                  & and F(s_i) attach(=, t: ?) s_(i+1)
      )
    $])
][
  Incrementally verifiable computation thus amounts to the secure computation; compressed to one accumulator, of repeated application of $F$ over $s_0$.

  #emph([Think: $F$ and $s$ are the payload of the secure compute by $IVC$. Note, $rivc$ contains $F$])
]

// s is value from COS
// F, s are the actual payload
// everything else guarantees secure compute of F and accumulation integrity of repeated application
// TODO how are polynomials encoded in a circuit; vec(R), vec(X).

#pagebreak(weak: true)

#slide(align: center + horizon)[
  $
    F(s) = ...
  $
][
  TODO: Chain of Signatures & catchup at a high level
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
    [#strong("C,E")], [type safe multi in out gates via properads],
    [#strong("O,E")], [rewriting of user defined algebraic identities],
    [#strong("E")], [elegant handling of transcript hash via index maps],
    [#strong("C,E")], [user extensible single source of truth scheme via spec],
    [#strong("C,O")], [relative wires; gate declaration invariant],
  )
]]

= Arithmetization

== Pipeline

#let interpolate = $text("interpolate")$
#let trace = $text("trace")$;
#let tracepub = $text("trace")_pub$;
#let build = $text("build")$;
$
  (vec(X), vec(R), vec(W)) & = arith(vec(w), IVC)      && = interpolate compose trace compose build \
          (vec(X), vec(R)) & = arith_pub (vec(x), IVC) && = interpolate compose tracepub compose build
$
#pause
TODO program > abstract circuit diagram > trace table > XRW

== Build

#align(center)[#emph([denotational semantics of a program is its abstract circuit])]

#let build(x) = $bracket.l.double #x bracket.r.double$;

$
  #build($x^2 + y = z^*$)
$

#pause

#align(center)[#emph([canonical programs as base cases])]

$
  =#build($x times x = t$)^s_s' and #build($t + y = z^*$)^s'_s''
$

TODO abstract circuit diagram AND relation

== Abstractions

#let Wire = $text("Wire")$;
#let Gate = $text("Gate")$;
#let ACirc = $text("ACirc")$;
#let TraceTable = $text("TraceTable")$;
#let CWire = $text("CellWire")$;
#let Prpd = $text("PrPd")$;
#let Spec = $text("Spec")$;
#table(
  columns: (auto, 1fr, 1fr, 1fr),
  inset: 10pt,
  align: horizon + center,
  table.header($text("lvl")$, $text("atomic")$, $text("local")$, $text("global")$),
  $0$, $w: FF_p$, $text("constraint")$, $T: TraceTable$,
  $1$, $hat(w): Wire$, $g: Gate$, $hat(f): ACirc$,
  $2$, $dash(w): CWire$, $hat(g): Prpd$, $S: Spec$,
)

TODO reuse pipeline diagram

#pagebreak(weak: true)

TODO index map: small trace table example, equation, F_GC eval

== Trace

#let lfp = $text("lfp")$;
#let copym = $text("copy")$;
#let gatem = $text("gate")$;
#let gatempub = $text("gate")_pub$;
#let resolvem = $text("resolve")$;
#let ty = $text("ty")$;

$
  trace = grayed(lfp)(resolvem(gatem(copym)), grayed(text("eq")), grayed(s_bot))
$

#text(size: 1em)[#table(
  columns: (2fr, 1fr, 1fr, 2fr),
  inset: 10pt,
  align: horizon + center,
  table.header($resolvem$, $gatem$, $gatempub$, $copym$),
  [vmap], table.cell(colspan: 2, [pre-constraints]), [loop],
  $hat(vec(Y))$, table.cell(colspan: 2, [$T$]), $vec(sigma)$,
)]

TODO visuals for stack, trace table, and permutation


== Interpolate

TODO
- root of unity and cosets
- fast fourier interpolation
- tie trace table to gate constraints
- tie permutation to copy constraints

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
