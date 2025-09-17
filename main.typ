#import "@preview/touying:0.6.1": *
#import themes.university: *

#import "@preview/numbly:0.1.0": numbly

#show: university-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Master's Thesis Examination],
    subtitle: [Light Node Catchup Using Incrementaly Verifiable Chain of Signatures - Plonk Arithmetization Formal Specification],
    author: [#strong[supervisor]: Diego Aranha, #strong[co-supervisor]: Hamidreza Khoshakhlagh #linebreak() #v(0em) Rasmus Kirk Jakobsen, #underline[Abdul Haliq Abdul Latiff]],
    date: datetime(year: 2025, month: 9, day: 26),
    institution: [Aarhus Universitet],
  ),
)

#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

== Outline <touying:hidden>

#components.adaptive-columns(outline(title: none, indent: 1em))

= Overview

== Light Node Catchup

== Plonk Language

== Plonk Protocol

== Motivation

= Plonk Arithmetization

== Build

== Abstractions

== Trace

== Trace: Resolve

== Trace: Gate

== Trace: Copy

== Interpolate

== Example

= Conclusion

= Future Work
