(** A selected element of a duplicate-free list is absent from its prefix. *)
Require Import skylabs.prelude.base.

Set Default Goal Selector "!".

Lemma nodup_nth_not_in_firstn {A} (xs : list A) n x :
  List.NoDup xs -> nth_error xs n = Some x -> ~ In x (firstn n xs).
Proof.
  intros Hdup. revert n.
  induction Hdup as [|a xs Hfresh Hdup IH]; intros [|n] Hnth;
    cbn in Hnth; try discriminate.
  { cbn. tauto. }
  cbn. intros [Heq|Hin].
  { subst a. apply Hfresh. eapply nth_error_In. exact Hnth. }
  { exact (IH n Hnth Hin). }
Qed.
