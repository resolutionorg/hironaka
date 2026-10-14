import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.Introduction
import Blueprint.SchemeVocabulary
import Blueprint.SchemeBlowUp
import Blueprint.ProjectiveMorphisms
import Blueprint.BlowUpSequences
import Blueprint.Manifolds
import Blueprint.Successions
import Blueprint.Spaces
import Blueprint.AlgebraicTheorems
import Blueprint.AnalyticTheorems
import Blueprint.StandardTheorems
import Blueprint.Conventions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Resolution of Singularities in Characteristic Zero" =>

This document presents the statements of the Lean library `hironaka`, a formalization over Mathlib
of resolution of singularities in characteristic zero: Hironaka's theorems of 1964 and the
functorial and analytic forms given later by Kollár, Włodarczyk, and Bierstone and Milman. Every
theorem it presents is proved in the library and checked by Lean's kernel. The document explains
what each theorem says, how the formal statement relates to the source it follows, and what every
definition used by the statements means; the proofs are only sketched.

The document has five parts. The introduction recalls what resolution of singularities and
principalization are, lists the theorems, and explains how to read a node. Two parts then describe
the objects and operations in terms of which the theorems are stated, one for schemes and one for
analytic geometry. The main theorems follow. They open with two statements whose files import
Mathlib only: resolution of a variety by a single blow-up, which is Hironaka's Main Theorem I, and
{citeAs Ati70}[the local monomialization of a real-analytic function]. Then come two strands: algebraic
schemes, with {citeAs Hir64}[Hironaka's Main Theorems I, II and II(N) and Corollaries 1 and 3],
{citeAs Kol07}[Kollár's functorial principalization and resolution and his strong resolution of a variety],
and {citeAs Wlo05}[Włodarczyk's embedded desingularization]; and analytic manifolds and spaces, with
Hironaka's Main Theorem II″(N), {citeAs BM97}[Bierstone–Milman's principalization],
{citeAs Wlo09}[Włodarczyk's functorial principalization and embedded desingularization], and the resolution of real-
and complex-analytic spaces {cite Kol07}[Theorem 45]. In the section of each theorem, the properties
it asserts and the inputs particular to it are stated before the theorem; a property asserted by
several theorems is stated at the first of them. The appendix holds a dictionary from the
classical notions to their names in Mathlib and the library, the conventions and the sources.
Every declaration on which a main theorem's statement depends is embedded at some node; the
dependency graph and the summary at the end are computed from the Lean declarations.

The library was produced by an automated formalization process, directed and audited at
Resolution, following the human-written sources of its bibliography.

{include 0 Blueprint.Introduction}

# Schemes
%%%
tag := "part-schemes"
file := "schemes"
%%%

The objects and operations in terms of which the algebraic theorems are stated: algebraic
$`k`-schemes, regularity, orders and normal crossings; the blow-up of a scheme along an ideal sheaf;
projective morphisms; and successions of blow-ups with
their transforms and boundaries, divisor families with simple normal crossings, the operations on
successions, and the blow-up sequence functors of the functorial theorems.

{include Blueprint.SchemeVocabulary}
{include Blueprint.SchemeBlowUp}
{include Blueprint.ProjectiveMorphisms}
{include Blueprint.BlowUpSequences}

# Analytic geometry
%%%
tag := "part-analytic"
file := "analytic-geometry"
%%%

The objects and operations in terms of which the analytic theorems are stated: analytic
manifolds with their ideal sheaves, submanifolds and blow-ups; finite successions, the compatible
families over the compact subsets of a manifold and the pull-back of a succession along a local
analytic isomorphism; and analytic spaces.

{include Blueprint.Manifolds}
{include Blueprint.Successions}
{include Blueprint.Spaces}

# Main theorems
%%%
tag := "part-theorems"
file := "theorems"
%%%

The main theorems of the library: first two stated in Mathlib's language, then two
strands, algebraic schemes over a field of characteristic zero and real- and complex-analytic
manifolds and spaces. Each section presents
one theorem: the properties it asserts and the inputs particular to it, then the theorem and a
sketch of its proof.

{include Blueprint.StandardTheorems}
{include Blueprint.AlgebraicTheorems}
{include Blueprint.AnalyticTheorems}

# Appendix
%%%
tag := "part-appendix"
file := "appendix"
%%%

A dictionary from the classical notions to their names in Mathlib and the library, the
conventions shared by the statements, and the sources.

{include Blueprint.Conventions}

{blueprint_graph}
{blueprint_summary}
{blueprint_bibliography}
