(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Own instances for iProp **)
(* TODO: these should be upstreamed to Iris. *)
Require Export iris.si_logic.bi.

Require Export iris.base_logic.lib.own. (* << exporting [inG] and [gFunctors] *)

Require Export bedrock.lang.bi.own.

(* Instances for iProp *)

(* Embedding of si in iProp. It seems that such an embedding doesn't exist
  upstream yet. *)
Section si_embedding.
  Context {Σ : gFunctors}.

  #[local] Arguments siProp_holds !_ _ /.
  #[local] Arguments uPred_holds !_ _ _ /.

  Notation iPropI := (iPropI Σ).
  Notation iProp  := (iProp Σ).

  #[global] Program Instance si_embed : Embed siPropI iPropI :=
    λ P, {| uPred_holds n x := P n |}.
  Solve Obligations with naive_solver eauto using siProp_closed.

  #[global] Instance si_embed_mono : Proper ((⊢) ==> (⊢)) (@embed siPropI _ _).
  Proof. intros ?? PQ. constructor => ??? /=. by apply PQ. Qed.

  #[global] Instance si_embed_ne : NonExpansive (@embed siPropI _ _).
  Proof. intros ??? EQ. constructor => ???? /=. by apply EQ. Qed.

  Program Definition si_unembed (P : iProp) : siProp :=
    {| siProp_holds n := P n ε |}.
  Next Obligation. simpl. intros P n1 n2 ??. by eapply uPred_mono; eauto. Qed.
  Instance si_unembed_ne : NonExpansive si_unembed.
  Proof. intros ??? EQ. constructor => ??. rewrite /=. by apply EQ. Qed.

  Lemma si_embed_unembed (P : siProp) : si_unembed (embed P) ≡ P.
  Proof. by constructor. Qed.

  #[local] Ltac unseal :=
    rewrite /bi_emp /= /uPred_emp /= ?uPred_pure_eq /=
            /bi_emp /= /siProp_emp /= ?siProp_pure_eq /=
            /bi_impl /= ?uPred_impl_eq /bi_impl /= ?siProp_impl_eq /=
            /bi_forall /= ?uPred_forall_eq /= /bi_forall /= ?siProp_forall_eq /=
            /bi_exist /= ?siProp_exist_eq /bi_exist /= ?uPred_exist_eq /=
            /bi_sep /= /siProp_sep ?siProp_and_eq /bi_sep /= ?uPred_sep_eq /=
            /bi_wand /= ?uPred_wand_eq /bi_wand /= /siProp_wand ?siProp_impl_eq /=
            /bi_persistently /= /siProp_persistently /bi_persistently /=
            ?uPred_persistently_eq.
  #[local] Ltac unseal' := constructor => ???; unseal.

  Definition siProp_embedding_mixin : BiEmbedMixin siPropI iPropI si_embed.
  Proof.
    split; try apply _.
    - intros P [EP]. constructor => ??. apply (EP _ ε). done. by unseal.
    - intros PROP' IN P Q.
      rewrite -{2}(si_embed_unembed P) -{2}(si_embed_unembed Q).
      apply (f_equivI si_unembed).
    - by unseal'.
    - intros ??. unseal' => PQ ??. eapply PQ; [done..|by eapply cmra_validN_le].
    - intros A Φ. by unseal'.
    - intros A Φ. by unseal'.
    - intros P Q. unseal'. split; last naive_solver.
      intros []. exists ε. eexists. by rewrite left_id.
    - intros P Q. unseal' => PQ ??.
      apply (PQ _ ε); [done|rewrite right_id; by eapply cmra_validN_le].
    - intros P. by unseal'.
  Qed.

  #[global] Instance siProp_bi_embed : BiEmbed siPropI iPropI :=
    {| bi_embed_mixin := siProp_embedding_mixin |}.
  #[global] Instance siProp_bi_embed_emp : BiEmbedEmp siPropI iPropI.
  Proof. constructor. intros. by rewrite /bi_emp /= /uPred_emp uPred_pure_eq. Qed.

  (* TODO: uPred_cmra_valid should have been defined as si_cmra_valid.
    This is to be fixed upstream. *)
  Lemma si_cmra_valid_validI `{inG Σ A} (a : A) :
    ⎡ si_cmra_valid a ⎤ ⊣⊢@{iPropI} uPred_cmra_valid a.
  Proof.
    constructor => ???. unseal.
    by rewrite si_cmra_valid_eq uPred_cmra_valid_eq.
  Qed.
End si_embedding.

Section iprop_instances.
  Context `{Hin: inG Σ A}.

  Notation iPropI := (iPropI Σ).

  Definition has_own_iprop_def : HasOwn iPropI A := {|
    own := base_logic.lib.own.own ;
    own_op := base_logic.lib.own.own_op ;
    own_mono := base_logic.lib.own.own_mono ;
    own_ne := base_logic.lib.own.own_ne ;
    own_timeless := base_logic.lib.own.own_timeless ;
    own_core_persistent := base_logic.lib.own.own_core_persistent ;
  |}.
  #[local] Definition has_own_iprop_aux : seal (@has_own_iprop_def). Proof. by eexists. Qed.
  #[global] Instance has_own_iprop : HasOwn iPropI A := has_own_iprop_aux.(unseal).
  Definition has_own_iprop_eq :
    @has_own_iprop = @has_own_iprop_def := has_own_iprop_aux.(seal_eq).

  Lemma uPred_cmra_valid_bi_cmra_valid (a : A) :
    (uPred_cmra_valid a) ⊣⊢@{iPropI} bi_cmra_valid a.
  Proof. constructor => n x ? /=. by rewrite si_cmra_valid_eq uPred_cmra_valid_eq. Qed.

  #[global] Instance has_own_valid_iprop : HasOwnValid iPropI A.
  Proof.
    constructor. intros. rewrite -uPred_cmra_valid_bi_cmra_valid.
    by rewrite has_own_iprop_eq /= base_logic.lib.own.own_valid.
  Qed.

  #[global] Instance has_own_update_iprop : HasOwnUpd iPropI A.
  Proof.
    constructor; rewrite has_own_iprop_eq /=.
    - by apply base_logic.lib.own.own_update.
    - setoid_rewrite (bi.affine_affinely (bi_pure _)).
      by apply base_logic.lib.own.own_alloc_strong_dep.
  Qed.
End iprop_instances.

Instance has_own_unit_iprop {Σ} {A : ucmraT} `{Hin: inG Σ A} :
  HasOwnUnit (iPropI Σ) A.
Proof. constructor; rewrite has_own_iprop_eq /=. by apply base_logic.lib.own.own_unit. Qed.
