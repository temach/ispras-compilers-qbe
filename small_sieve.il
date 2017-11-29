export function $sieve(w %n, l %prime) {
@fill0.cond
  %cond =w csgtw %n, 0
  jnz %cond, @fill0.body, @outer.exit

@fill0.body
  storeb 0, %prime

@fill0.exit
  %cond =w csgtw %n, 1
  jnz %cond, @outer.exit, @outer.exit

@outer.exit
  ret
}
