
Definition is_happy_spec (s : string) : Prop :=
  (String.length s < 3 -> False) /\
  (String.length s >= 3 ->
   (forall i : nat, i <= String.length s - 3 ->
    (String.get s i <> String.get s (i + 1) /\
     String.get s i <> String.get s (i + 2) /\
     String.get s (i + 1) <> String.get s (i + 2)))).
