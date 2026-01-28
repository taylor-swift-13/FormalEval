Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

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

Parameter mkStr : string -> Any.
Axiom mkStr_not_int : forall s n, ~ IsInt (mkStr s) n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [mkStr "hello"; mkStr "worldd"; mkStr "-22"; mkStr "htestlHECoIzOixTonw"; 
     mkStr "how"; mkStr "-2"; mkStr "you"; mkStr "htestlHECIzOixTonw"; 
     mkStr "hellhelloo"; mkStr "howatermelHECIzOixTonw"] 
    [].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_nonint; [apply mkStr_not_int | ]).
  apply fir_nil.
Qed.