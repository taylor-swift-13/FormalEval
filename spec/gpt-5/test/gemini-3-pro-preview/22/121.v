Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

(* Helpers for the test case injection *)
Parameter inj_int : Z -> Any.
Parameter inj_str : string -> Any.
Parameter inj_list : list Any -> Any.

Axiom IsInt_inj_int : forall z, IsInt (inj_int z) z.
Axiom IsInt_inj_list : forall l n, ~ IsInt (inj_list l) n.

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

Example test_filter_integers : 
  filter_integers_spec 
    [inj_int 1; 
     inj_list [inj_int 2; inj_str "3"]; 
     inj_list [inj_int 8]; 
     inj_list [inj_int 5; inj_int 6]; 
     inj_list [inj_int 7; inj_int 8]; 
     inj_int 9] 
    [1; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - apply IsInt_inj_int.
  - apply fir_cons_nonint.
    + apply IsInt_inj_list.
    + apply fir_cons_nonint.
      * apply IsInt_inj_list.
      * apply fir_cons_nonint.
        -- apply IsInt_inj_list.
        -- apply fir_cons_nonint.
           ++ apply IsInt_inj_list.
           ++ apply fir_cons_int with (n := 9).
              ** apply IsInt_inj_int.
              ** apply fir_nil.
Qed.