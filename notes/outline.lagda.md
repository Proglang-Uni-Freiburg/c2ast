-*- agda2 -*-

# Title: 

1. regular session types with equirecursion: ST⁼

T ::= S | Unit | T ⊗ T | T → T
S ::= end! | end? | !T.S | ?T.S | ⊕{ l: S_l } | &{ l: S_l } | μX. S | X

μX. S is guarded / contractive

define: dual S

## Type equivalence  T ≈ T

λ x → x : Unit ≈ᵀ Unit

f₁ : T₁ ≈ᵀ T₁′
f₂ : T₂ ≈ᵀ T₂′
--------------------
λ p → let (x₁, x₂) = p in (f₁ x₁, f₂ x₂)
: T₁ ⊗ T₂ ≈ᵀ T₁′ ⊗ T₂′

f₁ : T₁ ≈ᵀ T₁′
f₂ : T₂ ≈ᵀ T₂′
--------------------
λ p → f₂ ∘ p ∘ f₁⁻¹
: T₁ → T₂ ≈ᵀ T₁′ → T₂′

g : S₁ ≈ S₂
-------------------------------------------
λ c₁ → fork (λ (c₂ : dual S₂) → g (c₁, c₂))
;; λ c₂ → fork (λ (c₁ : dual S₁) → g⁻¹ (c₂, c₁))
: S₁ ≈ᵀ S₂


## Session type equivalence  S ≈ S

Argh: we really need
S₁ ≈ S₂  ↦   (S₁, dual S₂) → Unit
(swapped in the definition below)

λ (c₁ : end!, c₂ : end?) → let () = wait c₁ in terminate c₂
:
end! ≈ end!

f : T₁ ≈ T₂
g : S₁ ≈ S₂
-----------------
λ (c₁ : ? T₁.S₁ , c₂ : ! T₂. dual S₂) →  let (t₁, c₁) = receive c₁ in let c₂ = send c₂ (f t₁) in g (c₁, c₂)
:
? T₁.S₁ ≈ ? T₂.S₂

(∀ l) g_l : S₁_l ≈ S₂_l
----------------------------
λ (c₁,          c₂) →      case c₁ of { l: let c₂ = select l c2 in g_l (c₁, c₂) }
:
&{ l: S₁_l } ≈ &{ l: S₂_l }

g : S₁[ μX.S₁ / X ] ≈ S₂
--------------------
λ (c₁ : μX.S₁ , c₂ : dual S₂) → g (unroll c₁, c₂)
μX. S₁ ≈ S₂

g : S₁ ≈ S₂[ μX.S₂ / X ]
--------------------
λ (c₁ : S₁, c₂ : dual μX. S₂) → g (c₁, unroll c₂)
S₁ ≈ μX. S₂

## Examples

μX. !Int.X ≈ μX. !Int.X
----------------------------------------
!Int.μX. !Int.X ≈ !Int.μX. !Int.X         rec g₂ (c₁, c₂). let (t₁, c₁) = receive c₁ in let c₂ = send c₂ t₁ in g (c₁, c₂)
----------------------------------------
!Int.μX. !Int.X ≈ μX. !Int.X              rec g₁ (c₁, c₂). g₂ (c₁, unroll c₂)
----------------------------------------
μX. !Int.X ≈ μX. !Int.X                   rec g (c₁, c₂). g₁ (unroll c₁, c₂)

... taken altogether:	rec g (c₁, c₂). let (t₁, c₁) = receive (unroll c₁) in let c₂ = send (unroll c₂) t₁ in g (c₁, c₂)

μX. !Int.X ≈ μX. !Int.!Int.X

## Terms

M ::= x | λ x.M | M M | () | let () = M in M | (M, M) | let (x, y) = M in M
  | wait M | terminate M | send M M | receive M | select l M | case M of { l: M_l }

Standard conversion rule

Γ ⊢ M : S₁      S₁ ≈ S₂
-----------------------
Γ ⊢ M : S₂


## isorecursive version, ST≅


M ++= roll M | unroll M | fork M

Γ ⊢ M : S[ μX. S / X ]
----------------------
Γ ⊢ roll M : μX. S

Γ ⊢ M : μX. S
-----------------------------
Γ ⊢ unroll M : S[ μX. S / X ]

Γ ⊢ M : dual S → Unit
---------------------
Γ ⊢ fork M : S

## translation

Γ ⊢ M ~> M′ : S₁
g : S₁ ≈ S₂
------------------------------------------------
Γ ⊢ M ~> fork (λ (c : dual S₂) → g (M', c)) : S₂

## normalized derivations

### replace conversion with (iterated) top-level conversion: enough for wait, terminate, send, receive, select, case

Γ ⊢ M : μX. S
---------------------
Γ ⊢ M : S [μX. S / X]

### still need full conversion for arguments to functions and payload to send!

* maybe we do not need to synchronize roll and unroll between client and server?
* suppose a channel configuration (c, d) has the invariant c : S and d : S' and S and S' are dual modulo roll/unroll
* at Send/Receive reduction, inversion yields c : !T.S and d : ?T'.S' where !T.S and !T'.S' are dual modulo roll/unroll
* but discrepancies between T and T' need to be resolved by applying a coercion.
* (maybe we were too optimistic?)

## isorecursive → algebraic session types

This is a monadic function that returns a list of protocol types serving as argument list for a protocol constructor and
works over a writer monad that outputs a list of protocol definitions.
`new` generates a new name for a protocol; so there has to be a name generation monad, too.
(we could get away with a reader over [Label], where `local f` applies f to the environment)

collect⟦_⟧ : (ReaderMonad [Label] m, WriterMonad [ProtocolDef] m) ⇒ IST → Map Var Name → m [ProtocolArg]

collect⟦ μX. S ⟧ ρ  = n ← new; output( protocol n = {n-roll: local (n-roll ∷) (collect⟦ S ⟧ ρ[X ↦ n])} ); return [+n]
collect⟦ X ⟧ ρ = return [+ ρ X]
collect⟦ !T.S ⟧ ρ = s ← collect⟦ S ⟧; return (+ T) ∷ s
collect⟦ ?T.S ⟧ ρ = s ← collect⟦ S ⟧; return (- T) ∷ s
collect⟦ !end ⟧ ρ = return [+ Unit]             ???
collect⟦ ?end ⟧ ρ = return [- Unit]             ???
collect⟦ ⊕{ l: S_l } ⟧ ρ = n ← new; output( protocol n = {l: local (l ∷) (collect⟦ S_l ⟧ ρ)} ); return [+ n]
collect⟦ &{ l: S_l } ⟧ ρ = n ← new; output( protocol n = {l: local (l ∷) (collect⟦ S_l ⟧ ρ)} ); return [- n]

### Translation of terms (sketch)

* unroll → select n-roll (requires the context of the type translation or protocols with overloaded constructors)
* roll → ???
* terminate → send ()
* wait → receive

### Wire compatibility

(in isorecursive setting)

Define a relation ≈ between S and n where
[+ n] ← collect⟦ S ⟧ ∅
using the definitions stuffed in the writer.

TODO: lift this notion to the equirecursive setting (using optimized tagging: no tag transmission for single constructor protocols unless they are directly recursive; maybe further refinement needed)
TODO: characterize the image of collect and define a backtranslation for such regular protocols
TODO: define notion of wire compatibility / bisimulation for regular protocols
  (so we have a notion of compatibility of algebraic session types different from equality)
  (so we can claim that a traditional session type and its translation to AlgSt are wire compatible)
