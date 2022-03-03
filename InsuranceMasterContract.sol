pragma solidity ^0.4.8;
// ----------------------------------------------------------------------------------------------
// Sample fixed supply token contract
// Enjoy. (c) BokkyPooBah 2017. The MIT Licence.
// ----------------------------------------------------------------------------------------------
// ERC Token Standard #20 Interface
// https://github.com/ethereum/EIPs/issues/20
contract ERC20 {
    // Get the total token supply
    function totalSupply() constant returns (uint256 totalSupply);
    // Get the account balance of another account with address _owner
    function balanceOf(address _owner) constant returns (uint256 balance);
    // Send _value amount of tokens to address _to
    function transfer(address _to, uint256 _value) returns (bool success);
    // Send _value amount of tokens from address _from to address _to
    function transferFrom(address _from, address _to, uint256 _value) returns (bool success);
    // Allow _spender to withdraw from your account, multiple times, up to the _value amount.
    // If this function is called again it overwrites the current allowance with _value.
    // this function is required for some DEX functionality
    function approve(address _spender, uint256 _value) returns (bool success);
    // Returns the amount which _spender is still allowed to withdraw from _owner
    function allowance(address _owner, address _spender) constant returns (uint256 remaining);
    // Triggered when tokens are transferred.
    event Transfer(address indexed _from, address indexed _to, uint256 _value);
    // Triggered whenever approve(address _spender, uint256 _value) is called.
    event Approval(address indexed _owner, address indexed _spender, uint256 _value);
}

//
// Insurance Token is based on ERC20. The main difference is that it won't have fixed total supply since
// its emission is chained with emission of ICO token.
//
// For every ICO its own instance of InsuranceToken will be deployed.
//
// Investors will have the ability to see the Insurance tokens in their wallet but won't be able
// to sell them back to this contract (to recover their ETH) till this is unlocked by Insurer Company
// after Claim investigation.
//
contract InsuranceToken /*is ERC20*/ {
	string public constant symbol = "IST";
	string public constant name = "Insurance Token";
	uint8 public constant decimals = 18;
	uint insurancePercent = 10; // TODO should depend on ICO symbol
    bool isEligibleForReimburse = false;
	// Owner of this contract
    // This should be belonging to Insurance company
	address public owner;

	event Transfer(address indexed _from, address indexed _to, uint256 _value);
	event EligibleToReimburse(bool val);

	// Balances for each account
	mapping(address => uint256) balances;

	modifier onlyOwner() {
		if (msg.sender != owner) {
			throw;
		}
		_;
	}

	function InsuranceToken(/*string icoSymbol*/) {
		// TODO make it work
		//symbol = icoSymbol + "_INS";
		//name = icoSymbol + " Insurance Token";
		owner = msg.sender;
	}

//	function totalSupply() constant returns (uint256 totalSupply) {
//		return 0; // hmm
//	}

	function balanceOf(address _owner) constant returns (uint256 balance) {
		return balances[_owner];
	}

	function transfer(address _to, uint256 _amount) returns (bool success) {
		address thisContractAddress = address(this);

		if (balances[msg.sender] >= _amount
				&& _amount > 0
				&& balances[_to] + _amount > balances[_to]) {

			if (_to == thisContractAddress) { // reimburse transaction
				if (!isEligibleForReimburse)
					return false;

				// we send to investor the whole body of his investment in ETH
				uint amountToReimburseToInvestor = _amount / insurancePercent * 100;
				if (!_to.send(amountToReimburseToInvestor))
					return false;
			}

			balances[msg.sender] -= _amount;
			balances[_to] += _amount;
			Transfer(msg.sender, _to, _amount);
			return true;
		} else {
			return false;
		}
	}

	// not used
//	function transferFrom(address _from, address _to, uint256 _amount) returns (bool success) {
//		throw;
//	}

	// not used
//	function approve(address _spender, uint256 _amount) returns (bool success) {
//		throw;
//	}

	// not used
//	function allowance(address _owner, address _spender) constant returns (uint256 remaining) {
//		return 0;
//	}

	// issue insurance token to the investor in exchange to ETH
	function () payable {
		uint ethSentByCrowdsale = msg.value;
	    if (owner.send(ethSentByCrowdsale)) {
			balances[tx.origin] = ethSentByCrowdsale;
		}
	}

	function setEligibleForReimburse(bool val) onlyOwner {
		isEligibleForReimburse = val;
		EligibleToReimburse(val);
	}
}


contract Verifiable {
	function verify(address icoTokenAddr) constant returns (bool ok);
}

//
// Master contract through which Insurance Company creates and tracks all Insurance contracts.
//
contract InsuranceMasterContract is Verifiable {
    address owner;
    mapping(address => bool) tokensByAddress;
    mapping(string => bool) tokensBySymbol;

    function InsuranceMasterContract() {
        owner = msg.sender;
    }

    function createNew(string icoSymbol) {
        address token = new InsuranceToken();
        tokensByAddress[token] = true;
        tokensBySymbol[icoSymbol] = true;
    }

    function validateBySymbol(string icoSymbol) constant returns (bool) {
        return tokensBySymbol[icoSymbol];
    }
    function verify(address icoTokenAddr) constant returns (bool ok) {
        return tokensByAddress[icoTokenAddr];
    }
}
