Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition int := Z.

Parameter Any : Type.
Parameter IsInt : Any -> int -> Prop.

(* Injections for the types used in the test case *)
Parameter inj_Z : Z -> Any.
Parameter inj_Str : string -> Any.
Parameter inj_R : R -> Any.

Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

(* Axioms defining IsInt behavior for the injections *)
Axiom IsInt_inj_Z : forall z, IsInt (inj_Z z) z.
Axiom Not_IsInt_inj_Str : forall s n, ~ IsInt (inj_Str s) n.
Axiom Not_IsInt_inj_R : forall r n, ~ IsInt (inj_R r) n.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

(* Parameters for Real values to avoid decimal syntax issues *)
Parameter r_5_5 : R.
Parameter r_9_0 : R.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [inj_Z 1; inj_Z 2; inj_Z 3; inj_Str "8"; inj_R r_5_5; inj_Z 6; inj_Str "seven"; inj_Str "8"; inj_R r_9_0] 
    [1; 2; 3; 6].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1). apply IsInt_inj_Z.
  apply fir_cons_int with (n := 2). apply IsInt_inj_Z.
  apply fir_cons_int with (n := 3). apply IsInt_inj_Z.
  apply fir_cons_nonint. apply Not_IsInt_inj_Str.
  apply fir_cons_nonint. apply Not_IsInt_inj_R.
  apply fir_cons_int with (n := 6). apply IsInt_inj_Z.
  apply fir_cons_nonint. apply Not_IsInt_inj_Str.
  apply fir_cons_nonint. apply Not_IsInt_inj_Str.
  apply fir_cons_nonint. apply Not_IsInt_inj_R.
  apply fir_nil.
Qed.