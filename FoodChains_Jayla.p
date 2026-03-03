% Food Chains 

% Types 

% species & foodlink
tff(species_type, type, species: $tType).
tff(foodlink_type, type, foodlink: $tType).

% foodchain, complete_foodchain
tff(foodchain_type, type, foodchain: $tType).
tff(complete_foodchain_type, type, complete_foodchain: $tType).

% Symbols

% eats, eater, eaten
tff(eats_type,  type, eats: (species * species) > $o).
tff(eater_type, type, eater: foodlink > species).
tff(eaten_type, type, eaten: foodlink > species).

% primary_producer, apex_predator
tff(primary_producer_type, type, primary_producer: species > $o).
tff(apex_predator_type,   type, apex_predator: species > $o).

% start_of, end_of
tff(start_of_type, type, start_of: foodchain > species).
tff(end_of_type,   type, end_of:   foodchain > species).

% from complete_foodchain object to underlying foodchain
tff(as_foodchain_type, type, as_foodchain: complete_foodchain > foodchain).

% complete_foodchain 
tff(complete_chain_rel_type,type,
    complete_chain: ( species * species ) > $o ).

% depends
tff(depends_type, type, depends: (species * species) > $o).

% Axiom: The eater of a food link eats the eaten of the link.
tff(eater_of_link_eats_eaten, axiom,
    ! [L:foodlink] : eats(eater(L), eaten(L)) ).

% Axiom: The eaten and eater of a food link are not the same (no cannibalism).
tff(no_cannibalism, axiom,
    ! [L:foodlink] : eater(L) != eaten(L) ).

% Axiom: Every species eats something or is eaten by something (or both).
tff(eater_or_eaten, axiom,
    ! [S:species] :
      ( ? [T:species] : eats(S,T)
      | ? [U:species] : eats(U,S) ) ).

% Axiom: Something is a primary producer iff it eats no other species.
tff(primary_producer_def, axiom,
    ! [S:species] :
      ( primary_producer(S)
    <=> ! [T:species] : ~ eats(S,T) ) ).

% Theorem: If something is a primary producer then there is no food link such
% that the primary producer is the eater of the food link.
tff(primary_producer_not_eater, conjecture,
    ! [P:species] :
      ( primary_producer(P)
     => ! [L:foodlink] : eater(L) != P ) ).

% Theorem: Every primary producer is eaten by some other species.
tff(primary_producer_eaten, conjecture,
    ! [P:species] :
      ( primary_producer(P)
     => ? [S:species] : eats(S,P) ) ).

% Theorem: If a species is not a primary producer then there is another species that it eats.
tff(non_primary_producers_eat, conjecture,
    ! [S:species] :
      ( ~ primary_producer(S)
     => ? [T:species] : eats(S,T) ) ).

% Axiom: Something is an apex predator iff there is no species that eats it.
tff(apex_predator_def, axiom,
    ! [S:species] :
      ( apex_predator(S)
    <=> ! [T:species] : ~ eats(T,S) ) ).

% Theorem: If something is an apex predator then there is no food link such
% that the apex predator is the eaten of the food link.
tff(apex_predator_not_eaten, conjecture,
    ! [A:species] :
      ( apex_predator(A)
     => ! [L:foodlink] : eaten(L) != A ) ).

% Theorem: Every apex predator eats some other species.
tff(apex_predator_eats, conjecture,
    ! [A:species] :
      ( apex_predator(A)
     => ? [T:species] : eats(A,T) ) ).

% Theorem: If a species is not an apex predator then there is another species that eats it.
tff(non_apex_predator_eaten, conjecture,
    ! [S:species] :
      ( ~ apex_predator(S)
     => ? [T:species] : eats(T,S) ) ).

% Axiom: For every food chain, the start of the chain is the eaten of some food link,
% and one of the following holds:
% (i) the eater of the food link is the end of the food chain, or
% (ii) there is a shorter food chain from the eater of the food link to the end of the chain.
tff(foodchain_axiom, axiom,
    ! [C:foodchain] :
      ? [L:foodlink] :
        ( start_of(C) = eaten(L)
        & (
            ( (eater(L) = end_of(C))
              & ~ ? [C2:foodchain] :
                    ( start_of(C2) = eater(L)
                    & end_of(C2)   = end_of(C) )
            )
          | ( ~ (eater(L) = end_of(C))
              & ? [C2:foodchain] :
                    ( start_of(C2) = eater(L)
                    & end_of(C2)   = end_of(C) )
            )
          )
        )
).

% Axiom: There is no food chain from a species back to itself (no death spirals).
tff(no_death_spirals, axiom,
    ! [S:species] :
      ~ ? [C:foodchain] : ( start_of(C) = S & end_of(C) = S ) ).

% Axiom: A complete food chain starts at a primary producer, and ends at an apex predator.
tff(complete_chain_def, axiom,
    ! [S:species, E:species] :
      ( complete_chain(S,E)
    <=> ? [CC:complete_foodchain] :
          ( start_of(as_foodchain(CC)) = S
          & end_of(as_foodchain(CC))   = E
          & primary_producer(S)
          & apex_predator(E) ) )
).

% Axiom: Every species is in some complete food chain:
% (i) it is the primary producer start, or
% (ii) it is the apex predator end, or
% (iii) there is a non-complete food chain from start to the species, and another
%       non-complete food chain from the species to the end.
tff(all_species_in_complete_chain, axiom,
    ! [X:species] :
      ? [S:species, E:species] :
        ( complete_chain(S,E)
        & (
            X = S
          | X = E
          | ( ? [C1:foodchain, C2:foodchain] :
                ( start_of(C1) = S
                & end_of(C1)   = X
                & start_of(C2) = X
                & end_of(C2)   = E
                & X != S
                & X != E )
            )
          )
        )
).

% Theorem: No complete foodchain loops.
tff(no_complete_chain_loops, conjecture,
    ! [S:species, E:species] :
      ( complete_chain(S,E) => S != E )
).

% Theorem: The start species of a complete food chain does not eat the end species.
tff(start_species_not_eat_end_species, conjecture,
    ! [S:species, E:species] :
      ( complete_chain(S,E)
     => ~ eats(S,E) )
).

% Theorem: If a species is neither a primary producer nor an apex predator,
% then there is a food chain from a primary producer to that species,
% and another food chain from that species to an apex predator.
tff(in_the_middle_of_a_foodchain, conjecture,
    ! [X:species] :
      ( ( ~ primary_producer(X) & ~ apex_predator(X) )
     => ? [S:species, E:species, C1:foodchain, C2:foodchain] :
          ( complete_chain(S,E)
          & start_of(C1) = S
          & end_of(C1)   = X
          & start_of(C2) = X
          & end_of(C2)   = E ) )
).

% Axiom: Given two species, the first depends on the second iff there is a food chain
% from the second to the first.
tff(depends_axiom, axiom,
    ! [A:species, B:species] :
      ( depends(A,B)
    <=> ? [C:foodchain] : ( start_of(C) = B & end_of(C) = A ) )
).

% Theorem: If a species is not an apex predator then there is an apex predator that depends on the species.
tff(non_apex_predator, conjecture,
    ! [S:species] :
      ( ~ apex_predator(S)
     => ? [A:species] : ( apex_predator(A) & depends(A,S) ) )
).

% Theorem: An apex predator depends on all primary producers of all complete food chains that end at the apex predator.
tff(apex_predator_depends, conjecture,
    ! [A:species, P:species] :
      ( ( apex_predator(A)
        & primary_producer(P)
        & ? [S:species] : ( S = P & complete_chain(S,A) ) )
     => depends(A,P) )
).






