
Fibonacci in Haskell!! 

\begin{code}
fib :: Int -> Int
fib n = fib' 0 1 n
  where
    fib' a b 0 = a
    fib' a b n = fib' b (a+b) (n-1)
\end{code}

And here is a citation~\cite{deVries2014}, and another~\cite{Yakushev2009}!

LaTeX is setup!