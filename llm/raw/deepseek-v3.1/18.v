
Definition how_many_times_spec (string : string) (substring : string) (count : nat) : Prop :=
count = length (filter (fun i => substring =? substring_at string i substring) (seq 0 (length string))).

Definition substring_at (s : string) (start : nat) (sub : string) : bool :=
if Nat.ltb start (length s) then
  if Nat.leb (length sub) (length s - start) then
    substring s start (length sub) =? sub
  else false
else false.
