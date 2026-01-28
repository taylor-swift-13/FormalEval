Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive Any : Type :=
| AnyInt : Z -> Any
| AnyStr : string -> Any
| AnyList : list Any -> Any.

Definition int := Z.

Inductive IsInt : Any -> int -> Prop :=
| IsInt_intro : forall z, IsInt (AnyInt z) z.

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
    [AnyInt 1; 
     AnyList [AnyInt 2; AnyStr "3"]; 
     AnyList [AnyInt 4]; 
     AnyList [AnyInt 5; AnyInt 8; AnyInt 6; AnyInt 5; AnyInt 6]; 
     AnyList [AnyInt 5; AnyInt 8; AnyInt 6; AnyInt 5; AnyInt 6]; 
     AnyList [AnyInt 7; AnyInt 8]; 
     AnyInt 9; 
     AnyInt 1] 
    [1; 9; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - apply IsInt_intro.
  - apply fir_cons_nonint.
    + intros n H. inversion H.
    + apply fir_cons_nonint.
      * intros n H. inversion H.
      * apply fir_cons_nonint.
        -- intros n H. inversion H.
        -- apply fir_cons_nonint.
           ++ intros n H. inversion H.
           ++ apply fir_cons_nonint.
              ** intros n H. inversion H.
              ** apply fir_cons_int with (n := 9).
                 --- apply IsInt_intro.
                 --- apply fir_cons_int with (n := 1).
                     +++ apply IsInt_intro.
                     +++ apply fir_nil.
Qed.