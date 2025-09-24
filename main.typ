#import "@preview/touying:0.6.1": *
#import themes.university: *

#import "@preview/numbly:0.1.0": numbly
#import "@preview/circuiteria:0.2.0"

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
      script((q_i, acc_i) #h(0.5em) stretch(->) #h(0.5em) (q_(i+1), acc_(i+1))) \
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
  Computing commits uses scalar multiplication; $m G$, thus two fields; scalar $m: FF_cal(S)$ and base $G: EE(FF_cal(B))$. Pasta curves is a two cycle of curves where the scalar field of the other is its base field. This can express $m G$ as a circuit.

  #emph(
    [Think: A circuit has multiple types. If a circuit $vec(R)^((t))$ has canonical type $t$, then $vec(R)^((p))$ sets $t = p$ and $t'=q$],
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

  #emph([Think: $F$ and $s$ are the payload of the secure compute by $IVC$. Note, $F$ is embedded in $rivc$])
]

// s is value from COS
// F, s are the actual payload
// everything else guarantees secure compute of F and accumulation integrity of repeated application

#pagebreak(weak: true)

#let schnorr = [$text("SCHNORR")$];
#let schnorrsign = [$schnorr.#smallcaps("Sign")$];
#let schnorrverify = [$schnorr.#smallcaps("Verify")$];
#slide(align: center + horizon)[
  $
    F(s) = ... schnorrsign ...
  $
  #v(1em)
  #box(stroke: black, inset: 1em, [
    $
      script(text(#emoji.silhouette.double)_i #h(0.5em) attach(stretch(->), t: schnorrsign) #h(0.5em) text(#emoji.silhouette.double)_(i+1))
    $
    $
      sscript(Phi(text(#emoji.silhouette.double)_(i+1)) & = schnorrverify(text(#emoji.silhouette.double)_(i), text(#emoji.silhouette.double)_(i+1)))
    $])
][
  $s$ contains the current committee public key. $F$ is the current committee signing off the next committee.

  #emph(
    [Think: Instead of chain of blocks its chain of signatures (with block data). New committee provided via public inputs.],
  )
]

// Schnorr can be defined in terms of poseidon hashing thus $F$ is arithmetizable
// This does not solve problems of branching and finality. Same strategy as standard blockchains.

#pagebreak(weak: true)

#figure(
  image("./media/rivc_diagram.png", width: 100%),
)

== Plonk


#align(center)[#emph([
  PLONK is a #strong("S")uccint #strong("N")on-interactive #strong("AR")gument of #strong("K")nowledge

  Very small proofs of large statements
])]

#align(center)[$
  (vec(x), vec(w)) in R_IVC
$]
- *Witnesses* are input to programs; e.g. $IVC(vec(w))$
- *Public Inputs* are "_interfaces_" that behaviorally
  - assert values
  - instantiate / "_inject_" values

#text(size: 0.8em)[
  e.g. take the program $f(w) = (a times w) + w$, if $vec(x) = (a, a times w)$ then $((2,6),(3)) in vec(R)_f$.

  Here $a=2$ is injected, whereas $a times w=6$ is asserted.
]

// the witness isn't guaranteed private, not just due to the program structure, but also the polynomials aren't blinded. The SNARK simply serves as guarantee of correct computation.

#pagebreak(weak: true)

#let fgc = $F_(G C)$;
#let fgcplonk = $fgc^(cal("P")frak("lon")cal("K"))$;

#align(center)[$
  P arrow.r.squiggly V & : plonkprover(vec(X), vec(R), vec(W)) &               = & pi \
                     V & : plonkverifier(pi, vec(X), vec(R))   & attach(=, t: ?) & top
$]

#grid(
  columns: (1fr, 1fr),
  inset: 10pt,
  align: horizon,
  [
    1. *Gate Constraint Polynomial*
    2. Vanishing Argument
    3. Copy Constraints
    4. Grand Product Argument
    5. Batched Evaluation Proofs
  ],
  [
    #table(
      columns: (1fr, 1fr, 1fr, 1fr),
      align: horizon + center,
      inset: 10pt,
      table.cell(colspan: 4, $t$),
      $X$, $A_1$, $A_2$, $A_3$,
      $omega^1$, $1$, $2$, $3$, $omega^2$, $42$, $12$, $54$,
    )
    $
      F(X) = A_1(X) + A_2(X) - A_3(X)
    $
  ],
)

#pagebreak(weak: true)

#align(center)[$
  P arrow.r.squiggly V & : plonkprover(vec(X), vec(R), vec(W)) &               = & pi \
                     V & : plonkverifier(pi, vec(X), vec(R))   & attach(=, t: ?) & top
$]

#grid(
  columns: (1fr, 1fr),
  inset: 10pt,
  align: horizon,
  [
    1. Gate Constraint Polynomial
    2. *Vanishing Argument*
    3. Copy Constraints
    4. Grand Product Argument
    5. Batched Evaluation Proofs
  ],
  [
    $
      forall omega^i in H: F(omega^i) attach(=, t: ?) 0 \
      T(omega^i) = F(omega^i) / (Z_H (omega^i)) \
      v_F attach(=, t: ?) v_T times Z_H (xi)
    $
    #align(center)[
      #emph([
        $Z_H$ for factor theorem; $attach(=, t: ?) 0$

        $xi$ for Schwartz-Zippel; $F != 0$
      ])]
  ],
)

#pagebreak(weak: true)

#grid(
  columns: (1fr, 1fr),
  inset: 10pt,
  align: horizon,
  [
    #align(center)[#scale(70%)[$
      P arrow.r.squiggly V & : plonkprover(vec(X), vec(R), vec(W)) &               = & pi \
                         V & : plonkverifier(pi, vec(X), vec(R))   & attach(=, t: ?) & top
    $]]
    1. Gate Constraint Polynomial
    2. Vanishing Argument
    3. *Copy Constraints*
    4. Grand Product Argument
    5. Batched Evaluation Proofs
  ],
  [
    #scale(90%)[#circuiteria.circuit({
        import circuiteria: *
        gates.gate-and(x: 0, y: 1, w: 1, h: 1, id: "and")
        gates.gate-or(x: 2.7, y: 0, w: 1, h: 1, id: "or")
        wire.stub("and-port-in0", "west", length: 0.25, name: $a_1$)
        wire.stub("and-port-in1", "west", length: 0.25, name: $b_1$)
        wire.wire("w1", ("and-port-out", "or-port-in0"), style: "zigzag", name: ($$, $a_2$))
        wire.stub("or-port-in1", "west", length: 3.1, name: $b_2$)
        wire.stub("and-port-out", "east", length: 3.1, name: $c_1$)
        wire.stub("or-port-out", "east", length: 0.4, name: $c_2$)
      })
      $
        [a_1, b_1, bold(c_1), bold(a_2), b_2, c_2]
        &=^? [a_1, b_1, bold(a_2), bold(c_1), b_2, c_2] \
        sigma = [hat(c)_1 mapsto hat(a)_2, hat(a)_2 &mapsto hat(c)_1, w mapsto w] \
        {hat(a)_1, hat(b)_1, hat(c)_1, hat(a)_2, hat(b)_2, hat(c)_2} &=^? {hat(a)^sigma_1, hat(b)^sigma_1, hat(c)^sigma_1, hat(a)^sigma_2, hat(b)^sigma_2, hat(c)^sigma_2} \
        g(omega) dot g(omega^2) &=^? f(omega) dot f(omega^2) \
      $
    ]
  ],
)

#pagebreak(weak: true)

#align(center)[$
  P arrow.r.squiggly V & : plonkprover(vec(X), vec(R), vec(W)) &               = & pi \
                     V & : plonkverifier(pi, vec(X), vec(R))   & attach(=, t: ?) & top
$]

#grid(
  columns: (1fr, 1fr),
  inset: 10pt,
  align: horizon,
  [
    1. Gate Constraint Polynomial
    2. Vanishing Argument
    3. Copy Constraints
    4. *Grand Product Argument*
    5. Batched Evaluation Proofs
  ],
  [
    $
      product f(omega^i) & = product g(omega^i) \
            F_2(omega^n) & attach(=, t: ?) F_1(omega) attach(=, t: ?) 0 \
                  F_2(X) & = Z(X)f(X) - g(X) Z(omega X) \
                  F_1(X) & = L_1(X)(Z(X) - 1)
    $
    $
      Z(omega) = 1,
      Z(omega^(j+1)) = Z(omega^j) f(omega^j) / g(omega^j)
    $
  ],
)

#pagebreak(weak: true)


#align(center)[$
  P arrow.r.squiggly V & : plonkprover(vec(X), vec(R), vec(W)) &               = & pi \
                     V & : plonkverifier(pi, vec(X), vec(R))   & attach(=, t: ?) & top
$]

#grid(
  columns: (1fr, 1fr),
  inset: 10pt,
  align: horizon,
  [
    1. Gate Constraint Polynomial
    2. Vanishing Argument
    3. Copy Constraints
    4. Grand Product Argument
    5. *Batched Evaluation Proofs*
  ],
  [
    #scale(80%)[
      $
        W(X) = F_1(X) + alpha F_2(X) + alpha^2 F_3(X) + ...
      $
    ]
    #emph([Think: Combines proofs that "bind" evaluations to polynomial e.g.])
    $
       W(X) & = ...+ alpha (A(X) - A(xi)) + ... \
      W(xi) & attach(=, t: ?) 0
    $
  ],
)

// Note: F, F1, F2 are combined in vanishing as T. W simply checks evaluations at xi i.e. alpha^i(A(X) - v_A)
// And W_omega is 2nd batch open, for polys that are shifted by one, also use case for relative wires.

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
#let buildf = $text("build")$;
$
  (vec(X), vec(R), vec(W)) & = arith(vec(w), IVC)      && = interpolate compose trace compose buildf \
          (vec(X), vec(R)) & = arith_pub (vec(x), IVC) && = interpolate compose tracepub compose buildf
$
#pause

#let build(x) = $bracket.l.double #x bracket.r.double$;
#grid(
  columns: (1fr, 1fr, 1fr, 1fr),
  inset: 0pt,
  align: horizon + center,
  smallcaps("Program"), smallcaps("Build"), smallcaps("Trace"), smallcaps("Interpolate"),
  grid.cell(colspan: 4, v(0.5em)),
  $(a_1 times b_1) + b_2$,
  scale(60%)[#circuiteria.circuit({
      import circuiteria: *
      gates.gate-and(x: 0, y: 1, w: 1, h: 1, id: "and")
      gates.gate-or(x: 2.7, y: 0, w: 1, h: 1, id: "or")
      wire.stub("and-port-in0", "west", length: 0.25, name: $a_1$)
      wire.stub("and-port-in1", "west", length: 0.25, name: $b_1$)
      wire.wire("w1", ("and-port-out", "or-port-in0"), style: "zigzag", name: ($$, $a_2$))
      wire.stub("or-port-in1", "west", length: 3.1, name: $b_2$)
      wire.stub("and-port-out", "east", length: 3.1, name: $c_1$)
      wire.stub("or-port-out", "east", length: 0.4, name: $c_2$)
    })
  ],
  scale(50%)[#table(
    columns: (1fr, 1fr, 1fr, 1fr),
    align: horizon + center,
    inset: 10pt,
    table.cell(colspan: 4, $t$),
    $X$, $A_1$, $A_2$, $A_3$,
    $omega^1$, [], [], [], $omega^2$, [], [], [],
  )],
  $vec(X), vec(R), vec(W)$
)


== Build

#align(center)[#emph([denotational semantics of a program is its abstract circuit])]


$
  #build($x^2 + y = z^*$)
$

#pause

#align(center)[#emph([canonical programs as base cases])]

$
  =#build($x times x = t$)^s_s' and #build($t + y = z^*$)^s'_s''
$

#pause

#figure(
  image("./media/build_example.png",)
)

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

#grid(
  columns: (1fr, 1fr, 1fr),
  inset: 10pt,
  align: horizon + center,
  smallcaps("lvl 0"), smallcaps("lvl 1"), smallcaps("lvl 2"),
  scale(50%)[#table(
    columns: (1fr, 1fr, 1fr, 1fr),
    align: horizon + center,
    inset: 10pt,
    table.cell(colspan: 4, $t$),
    $X$, $A_1$, $A_2$, $A_3$,
    $omega^1$, [], [], [], $omega^2$, [], [], [],
  )],
  scale(70%)[#circuiteria.circuit({
      import circuiteria: *
      gates.gate-and(x: 0, y: 1, w: 1, h: 1, id: "and")
      gates.gate-or(x: 2.7, y: 0, w: 1, h: 1, id: "or")
      wire.stub("and-port-in0", "west", length: 0.25, name: $hat(a)_1$)
      wire.stub("and-port-in1", "west", length: 0.25, name: $hat(b)_1$)
      wire.wire("w1", ("and-port-out", "or-port-in0"), style: "zigzag", name: ($$, $hat(a)_2$))
      wire.stub("or-port-in1", "west", length: 3.1, name: $hat(b)_2$)
      wire.stub("and-port-out", "east", length: 3.1, name: $hat(c)_1$)
      wire.stub("or-port-out", "east", length: 0.4, name: $hat(c)_2$)
    })
  ],
  scale(50%)[#table(
    columns: (1fr, 1fr, 1fr, 1fr),
    align: horizon + center,
    inset: 10pt,
    table.cell(colspan: 4, $#math.accent(text("constraint"), "^") (hat(g))$),
    table.cell(colspan: 4, $t$),
    $X$, $A_1$, $A_2$, $A_3$,
    $omega^1$, [], [], []
  )],
)

#pagebreak(weak: true)

$
text("IMap") = 
(t: text("Color")) -> (c: text("Column")) -> X(t,c) -> Y(t,c)
$

#align(center)[
#emph([Note how trace tables and pre-constraints are index maps. $vec(X), vec(R), vec(W)$ too])
]

#pause

#grid(
  columns: (1fr, 1fr, 1fr),
  inset: 10pt,
  align: horizon + center,
  [#smallcaps("TraceTable") $T$],
  [#smallcaps("Constraint") $X$],
  [#smallcaps("Equation") $F$],
  scale(50%)[#table(
    columns: (1fr, 1fr, 1fr, 1fr),
    align: horizon + center,
    inset: 10pt,
    table.cell(colspan: 4, $t$),
    $X$, $A_1$, $A_2$, $A_3$,
    $omega^1$, $a$, $b$, $c$, $omega^2$, [], [], [],
  )],
  scale(50%)[#table(
    columns: (1fr, 1fr, 1fr),
    align: horizon + center,
    inset: 10pt,
    $A_1$, $A_2$, $A_3$,
    $a$, $b$, $c$
  )],
  $
    F(A) &= A_1 + A_2 - A_3 \
    F(X) &= a + b - c
  $
)

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

#table(
  columns: (1fr, 1fr, 1fr, 1fr, 1fr),
  inset: 10pt,
  align: horizon + center,
  table.cell(colspan: 2, smallcaps("resolve")),
  smallcaps("gate"),
  table.cell(colspan: 2, smallcaps("copy")),
  table.cell(colspan: 2, [vmap, $hat(vec(Y))$]),
  [$T$],
  table.cell(colspan: 2, [loop, $vec(sigma)$]),
  [$mat(hat(w)_n; dots.v; hat(w)_1) \ bot$],
  [$mat(hat(w)_n; dots.v; hat(w)_1) \ hat(w)_n mapsto w_n$],
  [$underline(g #h(0.25em) hat(w)_n) in hat(f)$
  #table(
    columns: (1fr),
    inset: 10pt,
    align: horizon + center,
    $T$,
    $dots.v$,
    $text("ctrn")(g)$
  )
  ],
  [$hat(w)_n mapsto {(i,A_j), ...}$],
  [$vec(sigma) \ mat(delim: "[", (i,A_j) mapsto p; dots.v) $]
)

// 1. we have a stack of wires to resolve, and value maps
// 2. if the gate that outputs the wire, has its inputs resolved, we can compute the values of its output, we then update the value map e.g. if the inputs to the add gate are resolved, we can use the canonical add program to compute the output.
// 3. with the values we can instantiate the pre-constraints and concat that to the trace table.
// 4. when a gate is resolved, we populate a set of coordinates (row and column in trace table) with the same wires. this is called a loop.
// 5. when all loops are computed, the permutation, is coordinates and its next, if it is last it will point to the first, if its alone, it points to itself.

== Interpolate

#align(center)[#emph([For each type $t$ e.g. $FF_q$ we find a $omega$ of order $>=$ number of constraints])]

$
H_0 = angle.l omega angle.r, H_1 = angle.l k_1 omega angle.r, ...
$

#pause

#align(center)[#emph([Each row indexed by $omega^i$; thus we fast fourier interpolate per column])]

$
  T^q (A_i): FF_q [X]
$

#pause

#align(center)[#emph([We split them to public input, selectors, and witnesses])]

$
  (vec(X), vec(R), vec(W)) = text("split")(T)
$


== Example

TODO: tie to motivation in overview
- poseidon gate
- message passing gate & public input gate

how to present a properad? full pre-constraints? rough sketch? give simple example first? jump to relative wires in poseidon? omit features just talk about use case in IVC?

= Conclusion

== Summary

- to implement IVC for light node catchup, we need a SNARK
- Plonk is a SNARK but needs an arithmetization scheme that is feasible
- The abstractions used to define arithmetization makes
  - some classes of bugs impossible
  - algebraic optimizations
  - clean expressivity e.g. index maps
  - primitives for proofs.
- The abstractions has use case beyond IVC, catchup and even plonk.

== Future Work

- Full specification (copy, interpolate, prover, verifier)
- Formal specification. In agda? hacspec?
- Properad and relative gate compute caching; abstraction level 2
- User domain specific algebraic optimization via egglog rewriting
- Dependent properads; table row count dependent properads
  - root of unity as a canonical program, not ad hoc in interpolate
  - optimal multi lookup (dynamic mina lookups)
- Correctness and Soundness proofs of arith in full generality.
