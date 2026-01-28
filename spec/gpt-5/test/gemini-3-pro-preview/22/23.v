Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter val_string : string -> Any.
Axiom val_string_not_int : forall s n, ~ IsInt (val_string s) n.

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

Example test_filter_integers_strings :
  filter_integers_spec
    (map val_string ["hello"; "how"; "world"; "how"; "test"; "you"])
    [].
Proof.
  unfold filter_integers_spec.
  simpl.
  apply fir_cons_nonint. apply val_string_not_int.
  apply fir_cons_nonint. apply val_string_not_int.
  apply fir_cons_nonint. apply val_string_not_int.
  apply fir_cons_nonint. apply val_string_not_int.
  apply fir_cons_nonint. apply val_string_not_int.
  apply fir_cons_nonint. apply val_string_not_int.
  apply fir_nil.
Qed.