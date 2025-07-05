def hello := "world"
--2024/12/21 関数型言語会

--基礎
#eval hello
#eval 1+1
#eval [1,2,3]

--定義する際はdefを用いる
--#eval　評価
--#Check 型を確認
--Lean := 型 :
--Haskell = 型::

--カリー化されている定義
def plus (x y : Nat) := x + y
#eval plus 1 2

--カリー化されていない定義
def plus2 (x :Nat × Nat) := x.1 + x.2
#eval plus2 (1,)

--カリー化
#eval (fun x : Nat => x) 6
#check (λ y : Nat ↦ (fun x : Nat => x)) 5
#eval (λ y : Nat ↦ (fun x : Nat => x+y)) 5 2
#eval ( λ x : Nat ↦ x+1) 10

--カリー化されることで部分適用が出来る
#eval List.map (plus 2) [1,2,3]

#check plus 1 2
#eval plus (plus 1 2) 3

#check (λ x : Nat ↦ λ y ↦ x + y)
