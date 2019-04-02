(**

This files proves that HSET (almost) forms a type category ([HSET_TypeCat]). As the
collection of types in context Γ don't form an hset it is not possible
to instantiate the CwF structure, however all of the other axioms of a
CwF have been formalized.

Contexts, written Γ ⊢, are modelled as HSETs and substitutions
are modelled by maps σ : Δ → Γ. So the identity
substitution is given by the identity map 1 : Γ → Γ
and composition of substitutions are given by composition of maps
σ · δ (note that the order is diagrammatic). So we
automatically get the equations:

<<
      1 · σ = σ · 1 = σ        (σ · δ) · τ = σ · (δ · τ)
>>

Types in context Γ, usually written Γ ⊢ A and written A : Γ ⊢ in the
formalization, are defined as families of HSETs over Γ. 
So A : Γ ⊢ means A : Γ -> HSET.

Terms a of type A in context Γ, usually written Γ ⊢ a : A and written
a : Γ ⊢ A in the formalization, are defined as sections of A. 

This is equivalent to sections s : Γ → Γ.A of the
projection map p : Γ.A → Γ (see [TermIn_to_TermInSection],
[TermInSection_to_TermIn]).

The operations then defined are:

<<
              Γ ⊢ A    σ : Δ → Γ
            ---------------------- ([subst_type])
                   Δ ⊢ Aσ


             Γ ⊢ a : A    σ : Δ → Γ
           -------------------------- ([subst_term)]
                 Δ ⊢ aσ : Aσ


                    Γ ⊢ A

                 ----------- ([ctx_ext])
                   Γ ⋆ A ⊢


                    Γ ⊢ A
               ----------------- ([ctx_proj])
                 p : Γ ⋆ A → Γ


                    Γ ⊢ A
              ------------------ ([ctx_last])
                Γ ⋆ A ⊢ q : Ap


             σ : Δ → Γ   Γ ⊢ A   Δ ⊢ a : Aσ
          ----------------------------------- ([subst_pair])
                (σ,a) : Δ → Γ ⋆ A


                  σ : Δ → Γ    Δ ⊢ A
                ---------------------- ([p_gen])
                  p_gen : Δ ⋆ A → Γ


                  σ : Δ → Γ    Γ ⊢ A
             ----------------------------- ([q_gen])
               Δ ⋆ Aσ ⊢ q_gen : A(p_gen)
>>

These satisfy the following equations:

<<
                       A1 = A            ([subst_type_id])

                    (Aσ)δ = A(σδ)        ([subst_type_comp])

                       a1 = a            ([subst_term_id])

                    (aσ)δ = a(σδ)        ([subst_term_comp])

                δ · (σ,a) = (δ · σ,aδ)   ([subst_pair_subst])

                (σ,a) · p = σ            ([subst_pair_p])

                   q(σ,a) = a            ([subst_pair_q])

                    (p,q) = 1            ([subst_pair_id])

        (p_gen,q_gen) · p = p · σ        ([q_gen_mor_p])
>>

And the last square is a pullback square ([isPullback_q_gen_mor]).

Written by: Anders Mörtberg, 2017

 *)
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.All.
Require Import TypeTheory.OtherDefs.CwF_Pitts.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
(* Require Import TypeTheory.ALV1.TypeCat. *)

Local Open Scope cat.

Section sets.


Definition SET_tt_structure : tt_structure SET.
Proof.
use tpair.  
- intro Γ.
  exact (pr1 Γ → SET).
- simpl.
  intros Γ A.
  exact (∏ (c : Γ), A c).
Defined.

  
Lemma SET_reindx_structure : reindx_structure SET_tt_structure.
Proof.
  unfold reindx_structure.
  use tpair.
  - cbn.
    intros Δ Γ A σ c.
    exact (A (σ c)).
-

  
  
Definition SET_tt_reindx_type_struct : tt_reindx_type_struct SET.
Admitted.

Lemma SET_reindx_laws : reindx_laws SET_tt_reindx_type_struct.
Admitted.

Print tt_structure.

(* This is commented as we cannot complete it *)
(* Definition PreShv_CwF : cwf_struct (PreShv C). *)
(* Proof. *)
(* exists PreShv_tt_reindx_type_struct. *)
(* mkpair. *)
(* - exists PreShv_reindx_laws. *)
(*   repeat split. *)
(*   + intros Γ A Δ σ a. *)
(*     exists (subst_pair_p hsC σ a). *)
(*     intermediate_path (transportf (λ x, Δ ⊢ x) *)
(*             (subst_type_pair_p hsC σ a) (subst_term hsC (subst_pair hsC σ a) (@ctx_last _ hsC _ A))). *)
(*     admit. (* this should be provable, but painful *) *)
(*     apply subst_pair_q. *)
(*   + intros Γ A Δ Θ σ1 σ2 a. *)
(*     exact (subst_pair_subst hsC σ1 σ2 a). *)
(*   + intros Γ A. *)
(*     apply (@subst_pair_id C hsC Γ A). *)
(* - repeat split. *)
(*   + apply (functor_category_has_homsets C^op HSET has_homsets_HSET). *)
(*   + intros Γ. *)
(*     admit. (* this is not provable! *) *)
(*   + intros Γ A. *)
(*     use isaset_total2. *)
(*     * repeat (apply impred_isaset; intro); apply setproperty. *)
(*     * intros a; repeat (apply impred_isaset; intro). *)
(*       apply isasetaprop, setproperty. *)
(* Admitted. *)

End CwF.