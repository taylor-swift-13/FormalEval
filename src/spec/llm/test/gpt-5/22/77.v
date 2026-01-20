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
Parameter empty : Any.
Parameter ho_2w : Any.
Parameter worldhowhowworldhow : Any.
Parameter test : Any.
Parameter you : Any.

Hypothesis hello_nonint : forall n, ~ IsInt hello n.
Hypothesis how_nonint : forall n, ~ IsInt how n.
Hypothesis world_nonint : forall n, ~ IsInt world n.
Hypothesis empty_nonint : forall n, ~ IsInt empty n.
Hypothesis ho_2w_nonint : forall n, ~ IsInt ho_2w n.
Hypothesis worldhowhowworldhow_nonint : forall n, ~ IsInt worldhowhowworldhow n.
Hypothesis test_nonint : forall n, ~ IsInt test n.
Hypothesis you_nonint : forall n, ~ IsInt you n.

Example test_case_strings: filter_integers_spec [hello; how; world; how; empty; ho_2w; worldhowhowworldhow; test; you] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [apply hello_nonint |].
  apply fir_cons_nonint; [apply how_nonint |].
  apply fir_cons_nonint; [apply world_nonint |].
  apply fir_cons_nonint; [apply how_nonint |].
  apply fir_cons_nonint; [apply empty_nonint |].
  apply fir_cons_nonint; [apply ho_2w_nonint |].
  apply fir_cons_nonint; [apply worldhowhowworldhow_nonint |].
  apply fir_cons_nonint; [apply test_nonint |].
  apply fir_cons_nonint; [apply you_nonint |].
  constructor.
Qed.