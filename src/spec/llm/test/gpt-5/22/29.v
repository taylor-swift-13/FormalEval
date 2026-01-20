Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

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

Parameter hello : Any.
Parameter how : Any.
Parameter world : Any.
Parameter empty_string : Any.
Parameter ho_2w : Any.
Parameter worldhow : Any.
Parameter test : Any.
Parameter you : Any.

Axiom hello_nonint : forall n, ~ IsInt hello n.
Axiom how_nonint : forall n, ~ IsInt how n.
Axiom world_nonint : forall n, ~ IsInt world n.
Axiom empty_string_nonint : forall n, ~ IsInt empty_string n.
Axiom ho_2w_nonint : forall n, ~ IsInt ho_2w n.
Axiom worldhow_nonint : forall n, ~ IsInt worldhow n.
Axiom test_nonint : forall n, ~ IsInt test n.
Axiom you_nonint : forall n, ~ IsInt you n.

Example test_case_strings: filter_integers_spec [hello; how; world; how; empty_string; ho_2w; worldhow; test; you] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact hello_nonint|].
  eapply fir_cons_nonint; [exact how_nonint|].
  eapply fir_cons_nonint; [exact world_nonint|].
  eapply fir_cons_nonint; [exact how_nonint|].
  eapply fir_cons_nonint; [exact empty_string_nonint|].
  eapply fir_cons_nonint; [exact ho_2w_nonint|].
  eapply fir_cons_nonint; [exact worldhow_nonint|].
  eapply fir_cons_nonint; [exact test_nonint|].
  eapply fir_cons_nonint; [exact you_nonint|].
  constructor.
Qed.