[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-22041afd0340ce965d47ae6ef1cefeee28c7c493a6346c4f15d667ab976d596c.svg)](https://classroom.github.com/a/VqUL4C8_)
<HR><!-- -------------------------------------------------------------------------------------- -->
<H2>Food Chains</H2>

Food chains describe the feeding relationships between species in a biotic community.
They show the transfer of material and energy from one <EM>species</EM> to another within an
ecosystem.
If one species <EM>eats</EM> another, there is an <EM>food link</EM> from the <EM>eaten of</EM>
the food link to the <EM>eater of</EM> the foodlink.
<EM>Apex predators</EM> are those species that are not eaten by any species.
<EM>Primary producers</EM> (also known as autotrophs) are those species that do not eat any
species - they are capable of producing complex organic substances (essentially "food") from an
energy source and inorganic materials.
A sequence of food links from a species to a species to a species, etc, forms a <EM>food chain</EM>
that starts at the eaten of the first link and ends at the eaten of the last link.
A <EM>complete</EM> food chain starts at a primary producer and ends at an apex predator.
An apex predator is <EM>dependent on</EM> all the species in all the food chains that lead to the
apex.
<P>
The food chain environment can be modeled in typed first order logic, and various theorems can
then be proved.
Here the axioms of the system are given in English, interspersed with theorems that can be proved
from the preceding axioms.
<UL>
<LI> Axiom: The eater of a food link eats the eaten of the link.
<LI> Axiom: The eaten and eater of a food link are not the same (no cannibalism).
<LI> Axiom: Every species eats something or is eaten by something (or both).
<LI> Axiom: Something is a primary producer iff it eats no other species.
<LI> Theorem: If something is a primary producer then there is no food link such that the primary
     producer is the eater of the food link.
<LI> Theorem: Every primary producer is eaten by some other species.
<LI> Theorem: If a species is not a primary producer then there is another species that it eats.
<LI> Axiom: Something is an apex predator iff there is no species that eats it.
<LI> Theorem: If something is an apex predator then there is no food link such that the apex
     predator is the eaten of the food link.
<LI> Theorem: Every apex predator eats some other species.
<LI> Theorem: If a species is not a apex predator then there is another species that eats it.
<LI> Axiom: For every food chain, the start of the chain is the eaten of some food link, and one
     of the following holds:
         (i) the eater of the food link is the end of the food chain,
     xor (ii) there is a shorter food chain (shorter by one food link) from the eater of the food
              link to the end of the whole food chain.
<LI> Axiom: There is no food chain from a species back to itself (no death spirals).
<LI> Axiom: A complete food chain starts at a primary producer, and ends at an apex predator.
<LI> Axiom: Every species is in some complete food chain, i.e.,
     (i) the species is the primary producer start of the complete food chain, or
     (ii) the species is the apex predator at the end of the complete food chain, or
     (iii) there is a non-complete food chain from the start of the complete food chain to the
           species, and another non-complete food chain from the species to the end of the
           complete food chain.
<LI> Theorem: The start species of a complete food chain does not eat the end species.
<LI> Theorem: If a species is neither a primary producer nor an apex predator, then there is a
     food chain from a primary producer to that species, and another food chain from that species
     to an apex predator.
<LI> Axiom: Given two species, the first depends on the second iff there is a food chain
     from the second to the first.
<LI> Theorem: If a species is not an apex predator then there is an apex predator that depends
     on the species.
<LI> Theorem: An apex predator depends on all primary producers of all complete food chains that
     end at the apex predator.
</UL>

<H3>You must ...</H3>
<UL>
<LI> Formulate the types, axioms, and theorems in TPTP TFF syntax.
<LI> Ensure that the axioms are consistent using an ATP system.
<LI> Prove the theorems using an ATP system.
</UL>
Submit one file containing all the axioms and conjectures, in the order they are listed above.
This assignment is worth 20% of the course assessment.
It will be graded according to <A HREF="MarkingScheme.md">this marking scheme</A>.
Please review the <A HREF="https://www.cs.miami.edu/home/geoff/Courses/CSC749-26S/Admin/">
policies on assessment</A> in the administration document.
<P>
<HR><!-- -------------------------------------------------------------------------------------- -->
