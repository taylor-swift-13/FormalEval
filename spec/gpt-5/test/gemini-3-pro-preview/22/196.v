Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj_int : int -> Any.
Parameter inj_str : string -> Any.
Parameter inj_list : list Any -> Any.
Parameter Z_to_int : Z -> int.

Axiom list_not_int : forall l n, ~ IsInt (inj_list l) n.

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
    [ inj_list [inj_int (Z_to_int 1%Z); inj_str "2"]
    ; inj_list [inj_str "3"; inj_list [inj_int (Z_to_int 4%Z); inj_str "5"]]
    ; inj_list []
    ; inj_list [inj_str "abc"; inj_str "def"]
    ; inj_list [inj_str "abc"; inj_str "def"]
    ] 
    [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply list_not_int.
  apply fir_cons_nonint. apply list_not_int.
  apply fir_cons_nonint. apply list_not_int.
  apply fir_cons_nonint. apply list_not_int.
  apply fir_cons_nonint. apply list_not_int.
  apply fir_nil.
Qed.