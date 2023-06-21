-*- agda2 -*-

# Title: 

1. regular session types with equirecursion: ST⁼

T ::= S | Unit | T ⊗ T | T → T
S ::= end! | end? | !T.S | ?T.S | ⊕{ l: S_l } | &{ l: S_l } | μX. S | X

μX. S is guarded

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
