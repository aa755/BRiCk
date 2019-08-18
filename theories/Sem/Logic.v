(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq.Classes Require Import
     RelationClasses Morphisms.


From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Semantics.
From Cpp.Auto Require Import
     Discharge.

Module Type logic.

  Parameter mpred : Type.

  Parameter ILogicOps_mpred : ILogicOps mpred.
  Global Existing Instance ILogicOps_mpred.
  Parameter ILogic_mpred : ILogic mpred.
  Global Existing Instance ILogic_mpred.

  Parameter BILogicOps_mpred : BILogicOps mpred.
  Global Existing Instance BILogicOps_mpred.
  Parameter BILogic_mpred : BILogic mpred.
  Global Existing Instance BILogic_mpred.

  Parameter EmbedOp_Prop_mpred : EmbedOp Prop mpred.
  Global Existing Instance EmbedOp_Prop_mpred.
  Parameter Embed_Prop_mpred : Embed Prop mpred.
  Global Existing Instance Embed_Prop_mpred.

  Parameter ILLOperators_mpred : ILLOperators mpred.
  Global Existing Instance ILLOperators_mpred.
  Parameter ILLater_mpred : ILLater mpred.
  Global Existing Instance ILLater_mpred.

  Notation "'[|'  P  '|]'" := (only_provable P).

  (** core assertions
   * note that the resource algebra contains the code memory as well as
   * the heap.
   *)

  Parameter with_genv : (genv -> mpred) -> mpred.
  Axiom with_genv_single : forall f g,
      with_genv f //\\ with_genv g -|- with_genv (fun r => f r //\\ g r).
  Axiom with_genv_single_sep : forall f g,
      with_genv f ** with_genv g -|- with_genv (fun r => f r ** g r).
  Axiom with_genv_ignore : forall P,
      with_genv (fun _ => P) -|- P.
  Declare Instance Proper_with_genv_lentails :
    Proper (pointwise_relation _ lentails ==> lentails) with_genv.
  Declare Instance Proper_with_genv_lequiv :
    Proper (pointwise_relation _ lequiv ==> lequiv) with_genv.

  (* heap points to *)
  (* note(gmm): this needs to support fractional permissions and other features *)
  Parameter tptsto : type -> forall addr value : val, mpred.

  Axiom tptsto_has_type : forall t a v,
      tptsto t a v |-- tptsto t a v ** [| has_type v t |].

  Parameter local_addr : region -> ident -> ptr -> mpred.

  (* the pointer contains the code *)
  Parameter code_at : Func -> ptr -> mpred.
  (* code_at is freely duplicable *)
  Axiom code_at_dup : forall p f, code_at p f -|- code_at p f ** code_at p f.
  Axiom code_at_drop : forall p f, code_at p f |-- empSP.

  Parameter ctor_at : ptr -> Ctor -> mpred.
  Parameter dtor_at : ptr -> Dtor -> mpred.

  (* todo(gmm): this should move to charge-core *)
  Section with_logic.
    Context {L : Type} {BIL : BILogicOps L}.
    Fixpoint sepSPs (ls : list L) : L :=
      match ls with
      | nil => empSP
      | l :: ls => l ** sepSPs ls
      end.
  End with_logic.

End logic.

Declare Module L : logic.

Export L.

Export ILogic BILogic ILEmbed Later.
