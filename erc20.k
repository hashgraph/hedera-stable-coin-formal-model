/* Ahthor: Grigore Rosu
   Date 2 December 2017

   ERC20-K is a formalization of the informal ERC20 standard at
   https://github.com/ethereum/EIPs/blob/master/EIPS/eip-20-token-standard.md

   See erc20.md for comments.  */

module ERC20-SYNTAX
  imports DOMAINS-SYNTAX
  
  syntax Value   ::= Int  // this can be changed
  syntax Address ::= Int  // this can be changed
  syntax AExp ::= Value | Address
                | "totalSupply" "(" ")"
                | "balanceOf" "(" AExp ")"                             [strict]
                | "allowance" "(" AExp "," AExp ")"                    [strict]
  syntax BExp ::= Bool
                | "constructor" "(" AExp "," AExp "," AExp "," AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")" [strict]
                | "approve" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                      [strict]
                | "transfer" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                     [strict]
                | "transferFrom" "(" AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")"        [strict]
                | "mint" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "burn" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "throw"
endmodule

module ERC20
  imports ERC20-SYNTAX
  imports DOMAINS

  configuration <ERC20 unused="true">
                  <k> $PGM:K </k>
                  <balances>
                    .Map
                  </balances>
                  <allowances>
                    <allowance multiplicity="*" type="Set" unused="true">
                      <owner> 0 </owner>
                      <spenders>
                        <allow multiplicity="*" type="Set" unused="true">
                          <spender> 0 </spender>
                          <amount> 0 </amount>
                        </allow>
                      </spenders>
                    </allowance>
                  </allowances>
                  <tokenName> 0 </tokenName>
                  <tokenSymbol> 0 </tokenSymbol>
                  <tokenDecimal> 0 </tokenDecimal>
                  <totalSupply> 0 </totalSupply>
                  <tokenOwner> 0 </tokenOwner>
                  <supplyManager> 0 </supplyManager>
                  <assetProtectionManager> 0 </assetProtectionManager>
                </ERC20>

  syntax KResult ::= Int | Bool | String

  syntax Int ::= "MAXVALUE"  [function]
  rule MAXVALUE => 2 ^Int 256 -Int 1

// base

  rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) => . ...</k>
      <tokenName> _ => TokenNameArg </tokenName>
      <tokenSymbol> _ => TokenSymbolArg </tokenSymbol>
      <tokenDecimal> _ => TokenDecimalArg </tokenDecimal>
      <totalSupply> _ => TotalSupplyArg </totalSupply>
      <tokenOwner> TokenOwner => Caller </tokenOwner>
      <supplyManager> _ => SupplyManagerArg </supplyManager>
      <assetProtectionManager> _ => AssetProtectionManagerArg </assetProtectionManager>
    requires TokenOwner ==Int 0
      andBool TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0

  // constructor throws if it's called more than once or arguments are incorrect
  rule <k> constructor(_, _, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) => throw ...</k>
      <tokenOwner> TokenOwner </tokenOwner>
    requires notBool (TokenOwner ==Int 0
      andBool TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0)
 
// getters

  rule <k> totalSupply() => Total ...</k>
      <totalSupply> Total </totalSupply>
      
  rule <k> balanceOf(Id) => (Balances[Id] orDefault 0) ...</k>
      <balances> Balances:Map  </balances>

  rule <k> allowance(Owner, Spender) => Allowance ...</k>
       <owner> Owner </owner>
       <spender> Spender </spender>
       <amount> Allowance </amount>

// erc20
/* 
  rule <k> approve(Spender, Allowance, { caller : Caller } ) => true ...</k>
       <owner> Caller </owner>
       <spender> Spender </spender>
       <amount> _ => Allowance </amount>
    requires Allowance >=Int 0

  rule <k> approve(_, Allowance, { caller : _ }) => throw ...</k>
    requires Allowance <Int 0

  rule <k> transfer(To, Value, { caller : Caller } ) => true ...</k>
       <account>
         <id> Caller </id>
         <balance> BalanceFrom => BalanceFrom -Int Value </balance>
       </account>
       <account>
         <id> To </id>
         <balance> BalanceTo => BalanceTo +Int Value </balance>
       </account>
    requires To =/=Int Caller    // sanity check
     andBool Value >=Int 0
     andBool Value <=Int BalanceFrom
     andBool BalanceTo +Int Value <=Int MAXVALUE

  rule <k> transfer(_, Value, { caller : Caller } ) => true ...</k>
       <id> Caller </id>
       <balance> BalanceFrom </balance>
    requires Value >=Int 0
     andBool Value <=Int BalanceFrom

  rule <k> transfer(To, Value, { caller : Caller } ) => throw ...</k>
       <account>
         <id> Caller </id>
         <balance> BalanceFrom </balance>
       </account>
       <account>
         <id> To </id>
         <balance> BalanceTo </balance>
       </account>
    requires To =/=Int Caller   // sanity check
     andBool (Value <Int 0
      orBool Value >Int BalanceFrom
      orBool BalanceTo +Int Value >Int MAXVALUE)

  rule <k> transfer(_, Value, { caller : Caller } ) => throw ...</k>
       <id> Caller </id>
       <balance> BalanceFrom </balance>
    requires Value <Int 0
      orBool Value >Int BalanceFrom

  rule <k> transferFrom(From, To, Value, { caller : Caller } ) => true ...</k>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance => Allowance -Int Value </amount>
       <account>
         <id> From </id>
         <balance> BalanceFrom => BalanceFrom -Int Value </balance>
       </account>
       <account>
         <id> To </id>
         <balance> BalanceTo => BalanceTo +Int Value </balance>
       </account>
    requires To =/=Int From    // sanity check
     andBool Value >=Int 0
     andBool Value <=Int BalanceFrom
     andBool Value <=Int Allowance   // `transfer` does not check allowance
     andBool BalanceTo +Int Value <=Int MAXVALUE

  rule <k> transferFrom(From, From, Value, { caller : Caller } ) => true ...</k>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance => Allowance -Int Value </amount>
       <id> From </id>
       <balance> BalanceFrom </balance>
    requires Value >=Int 0
     andBool Value <=Int BalanceFrom
     andBool Value <=Int Allowance   // `transfer` does not check allowance

  rule <k> transferFrom(From, To, Value, { caller : Caller } ) => throw ...</k>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance </amount>
       <account>
         <id> From </id>
         <balance> BalanceFrom </balance>
       </account>
       <account>
         <id> To </id>
         <balance> BalanceTo </balance>
       </account>
    requires To =/=Int From    // sanity check
     andBool (Value <Int 0
      orBool Value >Int BalanceFrom
      orBool Value >Int Allowance
      orBool BalanceTo +Int Value >Int MAXVALUE)

  rule <k> transferFrom(From, From, Value, { caller : Caller } ) => throw ...</k>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance </amount>
       <id> From </id>
       <balance> BalanceFrom </balance>
    requires Value <Int 0
      orBool Value >Int BalanceFrom
      orBool Value >Int Allowance   // `transfer` does not check allowance
*/
// mintable

  // note that according to the spec, the funds go to SupplyManager even if the caller is Owner
  rule <k> mint(Value, { caller : Caller } ) => . ...</k>
       <balances> ... (Caller |-> OldValue => Caller |-> OldValue +Int Value) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires 
      Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
  
  // NOTE: Kyc or a related function should have a side-effect of initiating balance. Might save a lot of headaches in mint/transfer. 
  //       Think we could get rid of this case if so.
  // I could not get K to let me combine this and the above function. The following expression wouldn't parse...
  // Balances [Caller <- (Value +Int (Balances[Caller] orDefault 0))]
  rule <k> mint(Value, { caller : Caller } ) => . ...</k>
       <balances> Balances:Map => Balances [Caller <- Value] </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires 
      Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
        andBool notBool (Caller in keys(Balances))

  rule <k> mint(Value, { caller : Caller } ) => throw ...</k>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply </totalSupply>
    requires 
      notBool (
        Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
      )
 
// burnable
  rule <k> burn(Value, {caller: Caller}) => . ...</k>
       <totalSupply> Supply => Supply -Int Value </totalSupply>
       <balances> ... (Caller |-> OldValue => Caller |-> OldValue -Int Value) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
    requires 
      OldValue >=Int Value
      andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
      andBool Value >=Int 0

endmodule
