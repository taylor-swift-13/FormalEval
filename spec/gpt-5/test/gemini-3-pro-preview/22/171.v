Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition int := Z.
Parameter Any : Type.
Parameter inj_int : int -> Any.
Parameter inj_list : list Any -> Any.
Parameter inj_bool : bool -> Any.

Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Axiom IsInt_inj_int : forall z, IsInt (inj_int z) z.
Axiom IsInt_not_list : forall l n, ~ IsInt (inj_list l) n.
Axiom IsInt_not_bool : forall b n, ~ IsInt (inj_bool b) n.

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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [ inj_list []
    ; inj_list []
    ; inj_list [inj_int 5%Z]
    ; inj_list [inj_bool true; inj_bool true; inj_bool true; inj_bool true; inj_bool false; inj_bool true; inj_bool true; inj_bool true; inj_bool true]
    ; inj_list [inj_int 7%Z; inj_int 8%Z]
    ; inj_int 9%Z
    ; inj_int 9%Z
    ; inj_list [inj_int 5%Z]
    ; inj_list [inj_int 5%Z]
    ]
    [9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply IsInt_not_list.
  apply fir_cons_nonint. apply IsInt_not_list.
  apply fir_cons_nonint. apply IsInt_not_list.
  apply fir_cons_nonint. apply IsInt_not_list.
  apply fir_cons_nonint. apply IsInt_not_list.
  apply fir_cons_int with (n := 9%Z). apply IsInt_inj_int.
  apply fir_cons_int with (n := 9%Z). apply IsInt_inj_int.
  apply fir_cons_nonint. apply IsInt_not_list.
  apply fir_cons_nonint. apply IsInt_not_list.
  apply fir_nil.
Qed.