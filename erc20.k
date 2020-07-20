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
                | "owner" "(" ")"
                | "supplyManager" "(" ")"
                | "assetProtectionManager" "(" ")"
                | "proposedOwner" "(" ")"
                | "balanceOf" "(" AExp ")"                             [strict]
                | "allowance" "(" AExp "," AExp ")"                    [strict]
  syntax BExp ::= Bool
                | "constructor" "(" AExp "," AExp "," AExp "," AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")" [strict]
                | "approve" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                      [strict]
                | "transfer" "(" AExp "," AExp "," "{" "caller" ":" AExp "}" ")"                     [strict]
                | "transferFrom" "(" AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")"        [strict]
                | "mint" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "burn" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "proposeOwner" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "claimOwnership" "(""{" "caller" ":" AExp "}" ")"            [strict]
                | "changeSupplyManager" "(" AExp "," "{" "caller" ":" AExp "}" ")"             [strict]
                | "changeAssetProtectionManager" "(" AExp "," "{" "caller" ":" AExp "}" ")"    [strict]
                | "isFrozen" "(" AExp ")"                                           [strict]
                | "isKycPassed" "(" AExp ")"                                        [strict]
                | "setKycPassed" "(" AExp "," "{" "caller" ":" AExp "}" ")"         [strict]
                | "unsetKycPassed" "(" AExp "," "{" "caller" ":" AExp "}" ")"       [strict]
                | "checkTransferAllowed" "(" AExp ")"                               [strict]
                | "freeze" "(" AExp "," "{" "caller" ":" AExp "}" ")"               [strict]
                | "unfreeze" "(" AExp "," "{" "caller" ":" AExp "}" ")"             [strict]
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
                  <frozen>
                    .Map
                  </frozen>
                  <kycpassed>
                    .Map
                  </kycpassed>
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
                  <proposedOwner> 0 </proposedOwner>
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

  rule <k> owner() => TokenOwner ...</k>
      <tokenOwner> TokenOwner </tokenOwner>

  rule <k> supplyManager() => SupplyManager ...</k>
      <supplyManager> SupplyManager </supplyManager>

  rule <k> assetProtectionManager() => AssetProtectionManager ...</k>
      <assetProtectionManager> AssetProtectionManager </assetProtectionManager>

  rule <k> proposedOwner() => ProposedOwner ...</k>
      <proposedOwner> ProposedOwner </proposedOwner>

  rule <k> allowance(Owner, Spender) => Allowance ...</k>
       <owner> Owner </owner>
       <spender> Spender </spender>
       <amount> Allowance </amount>

  rule <k> isFrozen(Id) => (Frozen[Id] orDefault false) ...</k>
      <frozen> Frozen:Map  </frozen>

  rule <k> isKycPassed(Id) => (KycPassed[Id] orDefault false) ...</k>
      <kycpassed> KycPassed:Map  </kycpassed>

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
       <balances> ... (SupplyManager |-> Balance => SupplyManager |-> Balance +Int Value) ... </balances>
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
       <balances> Balances:Map => Balances [SupplyManager <- Value] </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires
      Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
        andBool notBool (SupplyManager in keys(Balances))

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
       <balances> ... (SupplyManager |-> OldValue => SupplyManager |-> OldValue -Int Value) ... </balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
    requires
      OldValue >=Int Value
      andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
      andBool Value >=Int 0

// compliant

/* // jgorzny: isn't it true that if kyc is set, then account is in frozen?
  // allowed if passed kyc and frozen is unset
  rule <k> checkTransferAllowed(Account) => true ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> Frozen:Map </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
      andBool KycPassed
      andBool (notBool Account in keys(Frozen))
*/

  // allowed if passed kyc and frozen is set to false
  rule <k> checkTransferAllowed(Account) => true ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int 0
      andBool KycPassed
      andBool (notBool Frozen)

  // disallowed if passed kyc is unset or account is frozen
  rule <k> checkTransferAllowed(Account) => false ...</k>
      <kycpassed> KycPassed:Map </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool (notBool Account in keys(KycPassed))
      orBool Frozen

  // disallowed if passed kyc is set to false or account is frozen
  rule <k> checkTransferAllowed(Account) => false ...</k>
      <kycpassed> ... (Account |-> KycPassed) ... </kycpassed>
      <frozen> ... (Account |-> Frozen) ... </frozen>
      <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner ==Int 0
      orBool (notBool KycPassed)
      orBool Frozen

// privileged roles

  rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <proposedOwner> _ => ProposedOwner </proposedOwner>
    requires Caller =/=Int 0
      andBool ProposedOwner =/=Int 0

  rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int Caller
      orBool TokenOwner ==Int 0
      orBool ProposedOwner ==Int 0

  rule <k> claimOwnership( { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner => Caller </tokenOwner>
       <proposedOwner> Caller => 0 </proposedOwner>
    requires Caller =/=Int 0
      andBool TokenOwner =/=Int 0

  rule <k> claimOwnership( { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <proposedOwner> ProposedOwner </proposedOwner>
    requires ProposedOwner =/=Int Caller
      orBool TokenOwner ==Int 0

  rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <supplyManager> _ => SupplyManager </supplyManager>
    requires Caller =/=Int 0
      andBool SupplyManager =/=Int 0

  rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int Caller
      orBool TokenOwner ==Int 0
      orBool SupplyManager ==Int 0

  rule <k> changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } ) => . ...</k>
       <tokenOwner> Caller </tokenOwner>
       <assetProtectionManager> _ => AssetProtectionManager </assetProtectionManager>
    requires Caller =/=Int 0
      andBool AssetProtectionManager =/=Int 0

  rule <k> changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
    requires TokenOwner =/=Int Caller
      orBool TokenOwner ==Int 0
      orBool AssetProtectionManager ==Int 0

// unclassified

  // set kycpassed if the value is unset (i.e., set for the first time). Initializes frozen as well.
  rule <k> setKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> KycPassed => KycPassed[Account <- true] </kycpassed>
       <frozen> Frozen => Frozen[Account <- false] </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)
      andBool notBool (Account in keys(KycPassed))

  rule <k> setKycPassed(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  rule <k> setKycPassed(Account, { caller : _ } ) => throw ...</k>
       <kycpassed> ... (Account |-> true) ... </kycpassed>


  // set kycpassed if the value is false
  rule <k> setKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (Account |-> false => Account |-> true) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)


  // unset kycpassed
  rule <k> unsetKycPassed(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <kycpassed> ... (Account |-> true => Account |-> false) ... </kycpassed>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> unsetKycPassed(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  rule <k> unsetKycPassed(Account, { caller : _ } ) => throw ...</k>
       <kycpassed> KycPassed:Map </kycpassed>
    requires notBool (Account in keys(KycPassed))

  rule <k> unsetKycPassed(Account, { caller : _ } ) => throw ...</k>
       <kycpassed> ... (Account |-> false) ... </kycpassed>

  // freeze
  rule <k> freeze(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> false => Account |-> true) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> freeze(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  rule <k> freeze(Account, { caller : _ } ) => throw ...</k>
       <frozen> Frozen:Map </frozen>
    requires notBool (Account in keys(Frozen))

  rule <k> freeze(Account, { caller : _ } ) => throw ...</k>
       <frozen> ... (Account |-> true) ... </frozen>

  // unfreeze
  rule <k> unfreeze(Account, { caller : Caller } ) => . ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
       <frozen> ... (Account |-> true => Account |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool (Caller ==Int TokenOwner orBool Caller ==Int AssetProtectionManager)

  rule <k> unfreeze(_, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
    requires TokenOwner ==Int 0
      orBool (Caller =/=Int TokenOwner andBool Caller =/=Int AssetProtectionManager)

  rule <k> unfreeze(Account, { caller : _ } ) => throw ...</k>
       <frozen> Frozen:Map </frozen>
    requires notBool (Account in keys(Frozen))

  rule <k> unfreeze(Account, { caller : _ } ) => throw ...</k>
       <frozen> ... (Account |-> false) ... </frozen>

endmodule
