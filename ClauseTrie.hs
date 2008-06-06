
data Trie v = Nil
            | End
            | Node v Trie Trie Trie

asTrie :: (Num n) => [[n]] -> Trie n
asTrie [] = Nil
asTrie cs | any null cs = End
asTrie 