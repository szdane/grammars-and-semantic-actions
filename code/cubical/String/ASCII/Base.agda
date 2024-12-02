-- Subset of ASCII characters for writing test cases
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module String.ASCII.Base where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.SumFin
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as Empty
open import Cubical.Data.List as List
open import Cubical.Data.List.FinData


private
  variable
    ℓ' ℓ'' : Level

data ASCIIChar : Type ℓ-zero where
  SPACE NEWLINE TAB EXLCAM POUND
    SINGLEQUOTE DOUBLEQUOTE DOLLAR PERCENT
    AMPERSAND LPAREN RPAREN ASTERISK PLUS COMMA
    MINUS PERIOD FSLASH BSLASH COLON SEMICOLON
    GT EQ LT QUESTION AT LBRACKET RBRACKET CARROT
    UNDERSCORE BACKTICK TILDE LCURLY RCURLY VERTBAR
    A^ B^ C^ D^ E^ F^ G^ H^ I^ J^ K^ L^ M^
    N^ O^ P^ Q^ R^ S^ T^ U^ V^ W^ X^ Y^ Z^
    a^ b^ c^ d^ e^ f^ g^ h^ i^ j^ k^ l^ m^
    n^ o^ p^ q^ r^ s^ t^ u^ v^ w^ x^ y^ z^
    : ASCIIChar

open import String.Unicode
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

translation : List (UnicodeChar × ASCIIChar)
translation =
  (' ' , SPACE) ∷ ('\n' , NEWLINE) ∷ ('\t' , TAB) ∷
  ('!' , EXLCAM) ∷ ('#' , POUND) ∷
  ('\'' , SINGLEQUOTE) ∷ ('"' , DOUBLEQUOTE) ∷
  ('$' , DOLLAR) ∷ ('%' , PERCENT) ∷
  ('&' , AMPERSAND) ∷ ('(' , LPAREN) ∷
  (')' , RPAREN) ∷ ('*' , ASTERISK) ∷
  ('+' , PLUS) ∷ (',' , COMMA) ∷ ('-' , MINUS) ∷
  ('.' , PERIOD) ∷ ('/' , FSLASH) ∷
  ('\\' , BSLASH) ∷ (':' , COLON) ∷
  (';' , SEMICOLON) ∷ ('>' , GT) ∷ ('=' , EQ) ∷
  ('<' , LT) ∷ ('?' , QUESTION) ∷ ('@' , AT) ∷
  ('[' , LBRACKET) ∷ (']' , RBRACKET) ∷
  ('^' , CARROT) ∷ ('_' , UNDERSCORE) ∷
  ('`' , BACKTICK) ∷ ('~' , TILDE) ∷
  ('{' , LCURLY) ∷ ('}' , RCURLY) ∷
  ('|' , VERTBAR) ∷ ('A' , A^) ∷ ('B' , B^) ∷
  ('C' , C^) ∷ ('D' , D^) ∷ ('E' , E^) ∷
  ('F' , F^) ∷ ('G' , G^) ∷ ('H' , H^) ∷
  ('I' , I^) ∷ ('J' , J^) ∷ ('K' , K^) ∷
  ('L' , L^) ∷ ('M' , M^) ∷ ('N' , N^) ∷
  ('O' , O^) ∷ ('P' , P^) ∷ ('Q' , Q^) ∷
  ('R' , R^) ∷ ('S' , S^) ∷ ('T' , T^) ∷
  ('U' , U^) ∷ ('V' , V^) ∷ ('W' , W^) ∷
  ('X' , X^) ∷ ('Y' , Y^) ∷ ('Z' , Z^) ∷
  ('a' , a^) ∷ ('b' , b^) ∷ ('c' , c^) ∷
  ('d' , d^) ∷ ('e' , e^) ∷ ('f' , f^) ∷
  ('g' , g^) ∷ ('h' , h^) ∷ ('i' , i^) ∷
  ('j' , j^) ∷ ('k' , k^) ∷ ('l' , l^) ∷
  ('m' , m^) ∷ ('n' , n^) ∷ ('o' , o^) ∷
  ('p' , p^) ∷ ('q' , q^) ∷ ('r' , r^) ∷
  ('s' , s^) ∷ ('t' , t^) ∷ ('u' , u^) ∷
  ('v' , v^) ∷ ('w' , w^) ∷ ('x' , x^) ∷
  ('y' , y^) ∷ ('z' , z^) ∷ []

-- TODO move this
module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  (discA : Discrete A) where
  find : List (A × B) → (a : A) → Maybe B
  find [] the-a = nothing
  find ((a' , b') ∷ abs) the-a =
    decRec
      (λ _ → just b')
      (λ _ → find abs the-a)
      (discA a' the-a)

  findIdx : List (A × B) → (a : A) → ℕ → Maybe ℕ
  findIdx [] the-a n = nothing
  findIdx ((a' , b') ∷ abs) the-a n =
    decRec
      (λ _ → just n)
      (λ _ → findIdx abs the-a (suc n))
      (discA a' the-a)

Unicode→ASCII : UnicodeChar → Maybe ASCIIChar
Unicode→ASCII = find DiscreteUnicodeChar translation

_ : 87 ≡ length translation
_ = refl

ASCII→Fin : ASCIIChar → Fin 87
ASCII→Fin SPACE =       fromℕ {k = 86} 0
ASCII→Fin NEWLINE =     fromℕ {k = 86} 1
ASCII→Fin TAB =         fromℕ {k = 86} 2
ASCII→Fin EXLCAM =      fromℕ {k = 86} 3
ASCII→Fin POUND =       fromℕ {k = 86} 4
ASCII→Fin SINGLEQUOTE = fromℕ {k = 86} 5
ASCII→Fin DOUBLEQUOTE = fromℕ {k = 86} 6
ASCII→Fin DOLLAR =      fromℕ {k = 86} 7
ASCII→Fin PERCENT =     fromℕ {k = 86} 8
ASCII→Fin AMPERSAND =   fromℕ {k = 86} 9
ASCII→Fin LPAREN =      fromℕ {k = 86} 10
ASCII→Fin RPAREN =      fromℕ {k = 86} 11
ASCII→Fin ASTERISK =    fromℕ {k = 86} 12
ASCII→Fin PLUS =        fromℕ {k = 86} 13
ASCII→Fin COMMA =       fromℕ {k = 86} 14
ASCII→Fin MINUS =       fromℕ {k = 86} 15
ASCII→Fin PERIOD =      fromℕ {k = 86} 16
ASCII→Fin FSLASH =      fromℕ {k = 86} 17
ASCII→Fin BSLASH =      fromℕ {k = 86} 18
ASCII→Fin COLON =       fromℕ {k = 86} 19
ASCII→Fin SEMICOLON =   fromℕ {k = 86} 20
ASCII→Fin GT =          fromℕ {k = 86} 21
ASCII→Fin EQ =          fromℕ {k = 86} 22
ASCII→Fin LT =          fromℕ {k = 86} 23
ASCII→Fin QUESTION =    fromℕ {k = 86} 24
ASCII→Fin AT =          fromℕ {k = 86} 25
ASCII→Fin LBRACKET =    fromℕ {k = 86} 26
ASCII→Fin RBRACKET =    fromℕ {k = 86} 27
ASCII→Fin CARROT =      fromℕ {k = 86} 28
ASCII→Fin UNDERSCORE =  fromℕ {k = 86} 29
ASCII→Fin BACKTICK =    fromℕ {k = 86} 30
ASCII→Fin TILDE =       fromℕ {k = 86} 31
ASCII→Fin LCURLY =      fromℕ {k = 86} 32
ASCII→Fin RCURLY =      fromℕ {k = 86} 33
ASCII→Fin VERTBAR =     fromℕ {k = 86} 34
ASCII→Fin A^ =          fromℕ {k = 86} 35
ASCII→Fin B^ =          fromℕ {k = 86} 36
ASCII→Fin C^ =          fromℕ {k = 86} 37
ASCII→Fin D^ =          fromℕ {k = 86} 38
ASCII→Fin E^ =          fromℕ {k = 86} 39
ASCII→Fin F^ =          fromℕ {k = 86} 40
ASCII→Fin G^ =          fromℕ {k = 86} 41
ASCII→Fin H^ =          fromℕ {k = 86} 42
ASCII→Fin I^ =          fromℕ {k = 86} 43
ASCII→Fin J^ =          fromℕ {k = 86} 44
ASCII→Fin K^ =          fromℕ {k = 86} 45
ASCII→Fin L^ =          fromℕ {k = 86} 46
ASCII→Fin M^ =          fromℕ {k = 86} 47
ASCII→Fin N^ =          fromℕ {k = 86} 48
ASCII→Fin O^ =          fromℕ {k = 86} 49
ASCII→Fin P^ =          fromℕ {k = 86} 50
ASCII→Fin Q^ =          fromℕ {k = 86} 51
ASCII→Fin R^ =          fromℕ {k = 86} 52
ASCII→Fin S^ =          fromℕ {k = 86} 53
ASCII→Fin T^ =          fromℕ {k = 86} 54
ASCII→Fin U^ =          fromℕ {k = 86} 55
ASCII→Fin V^ =          fromℕ {k = 86} 56
ASCII→Fin W^ =          fromℕ {k = 86} 57
ASCII→Fin X^ =          fromℕ {k = 86} 58
ASCII→Fin Y^ =          fromℕ {k = 86} 59
ASCII→Fin Z^ =          fromℕ {k = 86} 60
ASCII→Fin a^ =          fromℕ {k = 86} 61
ASCII→Fin b^ =          fromℕ {k = 86} 62
ASCII→Fin c^ =          fromℕ {k = 86} 63
ASCII→Fin d^ =          fromℕ {k = 86} 64
ASCII→Fin e^ =          fromℕ {k = 86} 65
ASCII→Fin f^ =          fromℕ {k = 86} 66
ASCII→Fin g^ =          fromℕ {k = 86} 67
ASCII→Fin h^ =          fromℕ {k = 86} 68
ASCII→Fin i^ =          fromℕ {k = 86} 69
ASCII→Fin j^ =          fromℕ {k = 86} 70
ASCII→Fin k^ =          fromℕ {k = 86} 71
ASCII→Fin l^ =          fromℕ {k = 86} 72
ASCII→Fin m^ =          fromℕ {k = 86} 73
ASCII→Fin n^ =          fromℕ {k = 86} 74
ASCII→Fin o^ =          fromℕ {k = 86} 75
ASCII→Fin p^ =          fromℕ {k = 86} 76
ASCII→Fin q^ =          fromℕ {k = 86} 77
ASCII→Fin r^ =          fromℕ {k = 86} 78
ASCII→Fin s^ =          fromℕ {k = 86} 79
ASCII→Fin t^ =          fromℕ {k = 86} 80
ASCII→Fin u^ =          fromℕ {k = 86} 81
ASCII→Fin v^ =          fromℕ {k = 86} 82
ASCII→Fin w^ =          fromℕ {k = 86} 83
ASCII→Fin x^ =          fromℕ {k = 86} 84
ASCII→Fin y^ =          fromℕ {k = 86} 85
ASCII→Fin z^ =          fromℕ {k = 86} 86

-- This is incredibly ugly but works
-- Agda has issues pattern matching on nat literals
-- larger than 20, so I need to manually expand out
-- each num with its explicit constructors
-- It would be really nice to have some sort of macro
-- to define an enumerated type and automatically prove
-- that it is a FinSet
Fin→ASCII : Fin 87 → ASCIIChar
Fin→ASCII (fzero) = SPACE
Fin→ASCII (fsuc fzero) = NEWLINE
Fin→ASCII (fsuc (fsuc fzero)) = TAB
Fin→ASCII (fsuc (fsuc (fsuc fzero))) = EXLCAM
Fin→ASCII (fsuc ( fsuc (fsuc (fsuc fzero))  )) = POUND
Fin→ASCII (fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) )) = SINGLEQUOTE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) )) = DOUBLEQUOTE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) )) = DOLLAR
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) )) = PERCENT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) )) = AMPERSAND
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) )) = LPAREN
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) )) = RPAREN
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) )) = ASTERISK
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) )) = PLUS
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) )) = COMMA
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) )) = MINUS
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) )) = PERIOD
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) )) = FSLASH
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = BSLASH
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = COLON
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = SEMICOLON
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = GT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = EQ
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = LT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = QUESTION
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = AT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = LBRACKET
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = RBRACKET
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = CARROT
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = UNDERSCORE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = BACKTICK
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = TILDE
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = LCURLY
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = RCURLY
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = VERTBAR
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = A^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = B^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = C^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = D^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = E^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = F^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = G^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = H^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = I^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = J^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = K^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = L^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = M^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = N^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = O^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = P^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = Q^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = R^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = S^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = T^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = U^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = V^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = W^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = X^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = Y^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = Z^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = a^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = b^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = c^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = d^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = e^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = f^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = g^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = h^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = i^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = j^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = k^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = l^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = m^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = n^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = o^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = p^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = q^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = r^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = s^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = t^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = u^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = v^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = w^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = x^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = y^
Fin→ASCII (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = z^

ASCIIFinRetract : (c : ASCIIChar) → Fin→ASCII (ASCII→Fin c) ≡ c
ASCIIFinRetract SPACE = refl
ASCIIFinRetract NEWLINE = refl
ASCIIFinRetract TAB = refl
ASCIIFinRetract EXLCAM = refl
ASCIIFinRetract POUND = refl
ASCIIFinRetract SINGLEQUOTE = refl
ASCIIFinRetract DOUBLEQUOTE = refl
ASCIIFinRetract DOLLAR = refl
ASCIIFinRetract PERCENT = refl
ASCIIFinRetract AMPERSAND = refl
ASCIIFinRetract LPAREN = refl
ASCIIFinRetract RPAREN = refl
ASCIIFinRetract ASTERISK = refl
ASCIIFinRetract PLUS = refl
ASCIIFinRetract COMMA = refl
ASCIIFinRetract MINUS = refl
ASCIIFinRetract PERIOD = refl
ASCIIFinRetract FSLASH = refl
ASCIIFinRetract BSLASH = refl
ASCIIFinRetract COLON = refl
ASCIIFinRetract SEMICOLON = refl
ASCIIFinRetract GT = refl
ASCIIFinRetract EQ = refl
ASCIIFinRetract LT = refl
ASCIIFinRetract QUESTION = refl
ASCIIFinRetract AT = refl
ASCIIFinRetract LBRACKET = refl
ASCIIFinRetract RBRACKET = refl
ASCIIFinRetract CARROT = refl
ASCIIFinRetract UNDERSCORE = refl
ASCIIFinRetract BACKTICK = refl
ASCIIFinRetract TILDE = refl
ASCIIFinRetract LCURLY = refl
ASCIIFinRetract RCURLY = refl
ASCIIFinRetract VERTBAR = refl
ASCIIFinRetract A^ = refl
ASCIIFinRetract B^ = refl
ASCIIFinRetract C^ = refl
ASCIIFinRetract D^ = refl
ASCIIFinRetract E^ = refl
ASCIIFinRetract F^ = refl
ASCIIFinRetract G^ = refl
ASCIIFinRetract H^ = refl
ASCIIFinRetract I^ = refl
ASCIIFinRetract J^ = refl
ASCIIFinRetract K^ = refl
ASCIIFinRetract L^ = refl
ASCIIFinRetract M^ = refl
ASCIIFinRetract N^ = refl
ASCIIFinRetract O^ = refl
ASCIIFinRetract P^ = refl
ASCIIFinRetract Q^ = refl
ASCIIFinRetract R^ = refl
ASCIIFinRetract S^ = refl
ASCIIFinRetract T^ = refl
ASCIIFinRetract U^ = refl
ASCIIFinRetract V^ = refl
ASCIIFinRetract W^ = refl
ASCIIFinRetract X^ = refl
ASCIIFinRetract Y^ = refl
ASCIIFinRetract Z^ = refl
ASCIIFinRetract a^ = refl
ASCIIFinRetract b^ = refl
ASCIIFinRetract c^ = refl
ASCIIFinRetract d^ = refl
ASCIIFinRetract e^ = refl
ASCIIFinRetract f^ = refl
ASCIIFinRetract g^ = refl
ASCIIFinRetract h^ = refl
ASCIIFinRetract i^ = refl
ASCIIFinRetract j^ = refl
ASCIIFinRetract k^ = refl
ASCIIFinRetract l^ = refl
ASCIIFinRetract m^ = refl
ASCIIFinRetract n^ = refl
ASCIIFinRetract o^ = refl
ASCIIFinRetract p^ = refl
ASCIIFinRetract q^ = refl
ASCIIFinRetract r^ = refl
ASCIIFinRetract s^ = refl
ASCIIFinRetract t^ = refl
ASCIIFinRetract u^ = refl
ASCIIFinRetract v^ = refl
ASCIIFinRetract w^ = refl
ASCIIFinRetract x^ = refl
ASCIIFinRetract y^ = refl
ASCIIFinRetract z^ = refl

ASCIIFinSection : (n : Fin 87) → (ASCII→Fin (Fin→ASCII n)) ≡ n
ASCIIFinSection (fzero) = refl
ASCIIFinSection (fsuc fzero) = refl
ASCIIFinSection (fsuc (fsuc fzero)) = refl
ASCIIFinSection (fsuc (fsuc (fsuc fzero))) = refl
ASCIIFinSection (fsuc ( fsuc (fsuc (fsuc fzero))  )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl
ASCIIFinSection (fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc ( fsuc (fsuc (fsuc fzero))  ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )) = refl

isSetASCIIChar : isSet ASCIIChar
isSetASCIIChar =
  isSetRetract ASCII→Fin Fin→ASCII
    ASCIIFinRetract (isSetFin {87})

ASCII : hSet ℓ-zero
ASCII = ASCIIChar , isSetASCIIChar
-- isSetASCIIChar
ASCII≅Fin : Iso ASCIIChar (Fin 87)
ASCII≅Fin = iso ASCII→Fin Fin→ASCII ASCIIFinSection ASCIIFinRetract

ASCII≃Fin : ASCIIChar ≃ Fin 87
ASCII≃Fin = isoToEquiv ASCII≅Fin

isFinSetASCIIChar : isFinSet ASCIIChar
isFinSetASCIIChar = EquivPresIsFinSet (invEquiv ASCII≃Fin) (isFinSetFin {87})

DiscreteASCIIChar : Discrete ASCIIChar
DiscreteASCIIChar = isFinSet→Discrete isFinSetASCIIChar
