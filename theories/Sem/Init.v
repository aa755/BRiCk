(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Local Open Scope string_scope.
Local Open Scope Z_scope.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     ChargeUtil Logic PLogic Semantics Call Wp.

Module Type Init.

  Section with_resolve.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (resolve:=resolve) ti ρ).
    Local Notation wp_lval := (wp_lval (resolve:=resolve) ti ρ).
    Local Notation wp_rval := (wp_rval (resolve:=resolve) ti ρ).
    Local Notation wp_prval := (wp_prval (resolve:=resolve) ti ρ).
    Local Notation wp_xval := (wp_xval (resolve:=resolve) ti ρ).
    Local Notation wp_init := (wp_init (resolve:=resolve) ti ρ).
    Local Notation wp_args := (wp_args (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (resolve:=resolve) ti ρ).
    Local Notation fspec := (fspec (resolve:=resolve)).

    (** initialization lists *)
    Parameter wpi
    : forall {resolve : genv} (ti : thread_info) (ρ : region)
        (cls : globname) (this : val) (init : Initializer)
        (Q : mpred -> mpred), mpred.

    (* this is really about expression evaluation, so it doesn't make sense for
     * it to be recursive on a type.
     *)
    Fixpoint wp_initialize (ty : type) (addr : val) (init : Expr) (k : FreeTemps -> mpred)
    {struct ty} : mpred :=
      match ty with
      | Tvoid => lfalse
      | Tpointer _
      | Tbool
      | Tchar _ _
      | Tint _ _ =>
        wp_prval init (fun v free =>
                         _at (_eq addr) (uninit (erase_qualifiers ty)) **
                         (   _at (_eq addr) (tprim (erase_qualifiers ty) v)
                          -* k free))

        (* non-primitives are handled via prvalue-initialization semantics *)
      | Tarray ety sz => wp_init ty addr init k
      | Tref gn => wp_init ty addr init k
      | Treference t => lfalse (* reference fields are not supported *)
      | Trv_reference t => lfalse (* reference fields are not supported *)
      | Tfunction _ _ => lfalse (* functions not supported *)

      | Tqualified _ ty => wp_initialize ty addr init k
      end.

    Axiom wpi_initialize : forall this_val i cls Q,
        Exists a,
          _offsetL (offset_for cls i.(init_path)) (_eq this_val) &~ a ** ltrue //\\
        wp_initialize (erase_qualifiers i.(init_type)) a i.(init_init) Q
        |-- @wpi resolve ti ρ cls this_val i Q.

    Fixpoint wpis (cls : globname) (this : val)
             (inits : list Initializer)
             (Q : mpred -> mpred) : mpred :=
      match inits with
      | nil => Q empSP
      | i :: is => @wpi resolve ti ρ cls this i (fun f => f ** wpis cls this is Q)
      end.

    Axiom wp_init_constructor : forall cls addr cnd es Q ty,
      wp_args es (fun ls free =>
         Exists ctor, [| glob_addr resolve cnd ctor |] **
         |> fspec (Vptr ctor) (addr :: ls) ti (fun _ => Q free))
      |-- wp_init (Tref cls) addr (Econstructor cnd es ty) Q.

    Definition build_array (es : list Expr) (fill : option Expr) (sz : nat)
    : option (list (Z * Expr)) :=
      if Nat.ltb (List.length es) sz then
        match fill with
        | None => None
        | Some f =>
          Some (List.combine (List.map Z.of_nat (seq 0 sz))
                             (List.app es (map (fun _ => f) (seq (List.length es) (sz - 1)))))
        end
      else
        Some (List.combine (List.map Z.of_nat (seq 0 sz))
                           (firstn sz es)).

    Axiom wp_init_initlist_array :forall ls fill ety sz addr Q,
      match build_array ls fill (N.to_nat sz) with
      | None => lfalse
      | Some array_list =>
        _at (_eq addr) (uninit (erase_qualifiers (Tarray ety sz))) **
          wps (fun '(i,e) (Q : unit -> mpred -> mpred) f =>
                 Forall a, _offsetL (_sub ety i) (_eq addr) &~ a -*
                 wp_init ety a e (fun f' => Q tt (f ** f')))
              array_list
              (fun _ free => Q free) empSP
      end
      |-- wp_init (Tarray ety sz) addr (Einitlist ls fill (Tarray ety sz)) Q.

(*

    Axiom wp_init_wp_init' : forall addr ty init k,
        wp_init' addr ty init k -|- wp_init addr ty init k.
*)

    Axiom wp_init_bind_temp : forall e ty dtor loc ty' Q,
        wp_init loc ty e Q
        |-- wp_init loc ty (Ebind_temp e dtor ty') Q.
    Axiom wp_init_cast_noop : forall e ty loc ty' Q,
        wp_init loc ty e Q
        |-- wp_init loc ty (Ecast Cnoop (Rvalue, e) ty') Q.

    Axiom wp_init_clean : forall e ty ty' addr Q,
        wp_init ty' addr e Q
        |-- wp_init ty' addr (Eandclean e ty) Q.
    Axiom wp_init_const : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qconst ty) addr e Q.
    Axiom wp_init_mut : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qmut ty) addr e Q.

  End with_resolve.

End Init.

Declare Module IN : Init.

Export IN.
