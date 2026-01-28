Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj_str : string -> Any.
Axiom str_not_int : forall s n, ~ IsInt (inj_str s) n.

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

Example test_filter_integers_1 : filter_integers_spec [inj_str "hello"; inj_str "how"; inj_str "world"; inj_str ""; inj_str "ho-2w"; inj_str "worldhow"; inj_str "test"; inj_str "you"; inj_str "how"] [].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_nonint; [ apply str_not_int | ]).
  apply fir_nil.
Qed.