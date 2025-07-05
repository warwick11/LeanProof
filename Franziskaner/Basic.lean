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

-- 1章

-- 命題を表す型
inductive Prop' where
  -- 原子命題(これ以上分解できない)
  | P : String → Prop'
  -- 連言（かつ）
  | Con : Prop' → Prop' → Prop'
  -- 選言（または）
  | Dis : Prop' → Prop' → Prop'
  -- 含意（ならば）
  | Imp : Prop' → Prop' → Prop'
  deriving Repr
open Prop'

#check Imp (P "φ") (Imp (P "χ") (P "φ"))

-- 2章
variable (χ φ ψ : Prop)

-- φ : \phi
-- χ : \chi
-- ψ : \psi

-- ∧ : \and
-- ∨ : \or
-- → : \r
-- ¬ : \neg
-- ⊥ : \bot
-- ⊤ : \top

-- 2.1
-- applyは命題をゴールに適用する
example (p : φ ∧ χ) : (φ ∧ χ) := by
  apply p
  done

-- 命題を全部使用しなくても証明を書くことができる（警告はされる）
example (p : φ) (q : χ) : χ := by
  apply q
  done

------------------
--- かつの導入
------------------

-- `And.intro` は `∧` の導入規則
example (p : φ) (q : χ) : (φ ∧ χ) := by
  have r := And.intro p q
  apply r
  done

------------------
--- かつの除去
------------------

-- `And.left` は `∧` の左側の成分を取り出す
-- `And.right` は `∧` の右側の成分を取り出す
example (p : φ ∧ χ) : (χ ∧ φ) := by
  have l := And.left p
  have r := And.right p
  have f := And.intro r l
  apply f
  done

-- 別の書き方： `constructor` 使う
example (p : φ ∧ χ) : (χ ∧ φ) := by
  constructor
  . apply And.right p
  . apply And.left p
  done

------------------
--- またはの導入
------------------

-- `Or.inl` は `∨` の左側の成分から構成
-- `Or.inr` は `∨` の右側の成分から構成
example (p : φ ∧ χ) : (φ ∧ χ) ∨ (φ ∧ ψ) := by
  -- haveで束縛する場合は右側の型を明示的に指定してあげる必要がある
  have l : (φ ∧ χ) ∨ (φ ∧ ψ) := Or.inl p
  -- have r : (φ ∧ ψ) ∨ (φ ∧ χ) := Or.inr p
  apply l
  done

------------------
--- またはの除去
------------------

-- またはの除去は場合分けしてあげる必要がある
-- `case`
example (p : φ ∨ χ) : (χ ∨ φ):= by
  cases p with
  | inl p1 => apply Or.inr p1
  | inr p2 => apply Or.inl p2
  done
