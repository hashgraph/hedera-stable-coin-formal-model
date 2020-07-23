requires "erc20.k"

module BASE-SPEC
imports ERC20

// constructor should initialize all fields correctly
rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) =>  . ...</k>
     <balances> Balances:Map => Balances [SupplyManagerArg <- TotalSupplyArg] </balances>
     <kycpassed> KycPassed => KycPassed[Caller <- true][SupplyManagerArg <- true][AssetProtectionManagerArg <- true] </kycpassed>
     <tokenName> _ => TokenNameArg </tokenName>
     <tokenSymbol> _ => TokenSymbolArg </tokenSymbol>
     <tokenDecimal> _ => TokenDecimalArg </tokenDecimal>
     <totalSupply> _ => TotalSupplyArg </totalSupply>
     <tokenOwner> 0 => Caller </tokenOwner>
     <supplyManager> _ => SupplyManagerArg </supplyManager>
     <assetProtectionManager> _ => AssetProtectionManagerArg </assetProtectionManager>
     <proposedOwner> 0 </proposedOwner>
requires TokenDecimalArg >=Int 0
  andBool TotalSupplyArg >=Int 0
  andBool Caller =/=Int 0
  andBool SupplyManagerArg =/=Int 0
  andBool AssetProtectionManagerArg =/=Int 0

// if the TokenOwner has already been set, the constructor should throw
rule <k> constructor(_:Int, _:Int, _:Int, _:Int, _:Int, _:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
requires TokenOwner =/=Int 0
  andBool Caller =/=Int 0

// if the constructor is called twice in a row, the resulting state will only reflect the first call
rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } )
         ~>
         constructor(_:Int, _:Int, _:Int, _:Int, _:Int, _:Int, { caller : _:Int } ) => throw ...</k>
     <balances> Balances:Map => Balances [SupplyManagerArg <- TotalSupplyArg] </balances>
     <kycpassed> KycPassed => KycPassed[Caller <- true][SupplyManagerArg <- true][AssetProtectionManagerArg <- true] </kycpassed>
     <tokenName> _ => TokenNameArg </tokenName>
     <tokenSymbol> _ => TokenSymbolArg </tokenSymbol>
     <tokenDecimal> _ => TokenDecimalArg </tokenDecimal>
     <totalSupply> _ => TotalSupplyArg </totalSupply>
     <tokenOwner> TokenOwner => Caller </tokenOwner>
     <supplyManager> _ => SupplyManagerArg </supplyManager>
     <assetProtectionManager> _ => AssetProtectionManagerArg </assetProtectionManager>
     <proposedOwner> 0 </proposedOwner>
requires TokenOwner ==Int 0
  andBool TokenDecimalArg >=Int 0
  andBool TotalSupplyArg >=Int 0
  andBool Caller =/=Int 0
  andBool SupplyManagerArg =/=Int 0
  andBool AssetProtectionManagerArg =/=Int 0
 
endmodule