module Main

foo' : String
foo' = "hello"

foox27 : String
foox27 = "world"

main : IO ()
main = putStrLn $ foo' ++ ", " ++ foox27

