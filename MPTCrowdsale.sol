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

contract MPTICOToken is ERC20 {
    string public constant symbol = "MPTICO";
    string public constant name = "MPT ICO Token";
    uint8 public constant decimals = 18;
    uint256 _totalSupply = 1000000;
    // Owner of this contract
    address public owner;
    // Balances for each account
    mapping(address => uint256) balances;
    // Owner of account approves the transfer of an amount to another account
    mapping(address => mapping (address => uint256)) allowed;
    // Functions with this modifier can only be executed by the owner
    modifier onlyOwner() {
        if (msg.sender != owner) {
            throw;
        }
        _;
    }
    // Constructor
    function MPTICOToken() {
        owner = msg.sender;
        balances[owner] = _totalSupply;
    }
    function totalSupply() constant returns (uint256 totalSupply) {
        totalSupply = _totalSupply;
    }
    // What is the balance of a particular account?
    function balanceOf(address _owner) constant returns (uint256 balance) {
        return balances[_owner];
    }
    // Transfer the balance from owner's account to another account
    function transfer(address _to, uint256 _amount) returns (bool success) {
        if (balances[msg.sender] >= _amount
        && _amount > 0
        && balances[_to] + _amount > balances[_to]) {
            balances[msg.sender] -= _amount;
            balances[_to] += _amount;
            Transfer(msg.sender, _to, _amount);
            return true;
        } else {
            return false;
        }
    }
    // Send _value amount of tokens from address _from to address _to
    // The transferFrom method is used for a withdraw workflow, allowing contracts to send
    // tokens on your behalf, for example to "deposit" to a contract address and/or to charge
    // fees in sub-currencies; the command should fail unless the _from account has
    // deliberately authorized the sender of the message via some mechanism; we propose
    // these standardized APIs for approval:
    function transferFrom(
    address _from,
    address _to,
    uint256 _amount
    ) returns (bool success) {
        if (balances[_from] >= _amount
        && allowed[_from][msg.sender] >= _amount
        && _amount > 0
        && balances[_to] + _amount > balances[_to]) {
            balances[_from] -= _amount;
            allowed[_from][msg.sender] -= _amount;
            balances[_to] += _amount;
            Transfer(_from, _to, _amount);
            return true;
        } else {
            return false;
        }
    }

    // Allow _spender to withdraw from your account, multiple times, up to the _value amount.
    // If this function is called again it overwrites the current allowance with _value.
    function approve(address _spender, uint256 _amount) returns (bool success) {
        allowed[msg.sender][_spender] = _amount;
        Approval(msg.sender, _spender, _amount);
        return true;
    }

    function allowance(address _owner, address _spender) constant returns (uint256 remaining) {
        return allowed[_owner][_spender];
    }
}



//
// Insurance Token is based on ERC20. The main difference is that it won't have fixed total supply since
// its emission is chained with emission of MPT ICO token.
//
// For every ICO its own instance of InsuranceToken will be deployed.
//
// Investors will have the ability to see the Insurance tokens in their wallet but won't be able
// to sell them back to this contract (to recover their ETH) till this is unlocked by Insurer Company
// after Claim investigation.
//
contract InsuranceToken /*is ERC20*/ {
	string public constant symbol = "INS";
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



contract Crowdsale {
	address public beneficiary;
	uint public fundingGoal;
	uint public amountRaised;
	uint public deadline;
	uint public price;
	MPTICOToken public tokenReward;
	address insurerAddr;
	InsuranceToken public tokenInsurer;
	mapping(address => uint256) public balanceOf;
	bool fundingGoalReached = false;
	event GoalReached(address beneficiary, uint amountRaised);
	event FundTransfer(address backer, uint amount, bool isContribution);
	bool crowdsaleClosed = false;

	uint insurancePercent = 10; // TODO should depend on ICO symbol

	/* data structure to hold information about campaign contributors */

	/*  at initialization, setup the owner */
	function Crowdsale(
//		address ifSuccessfulSendTo,
		uint fundingGoalInEthers,
		uint durationInMinutes,
		uint etherCostOfEachToken,
		address _insurerAddr,
		MPTICOToken _tokenReward
	) {
//		beneficiary = ifSuccessfulSendTo;
		beneficiary = msg.sender;
		fundingGoal = fundingGoalInEthers * 1 ether;
		deadline = now + durationInMinutes * 1 minutes;
		price = etherCostOfEachToken * 1 ether;
		insurerAddr = _insurerAddr;
        tokenInsurer = InsuranceToken(_insurerAddr);
		tokenReward = _tokenReward;
	}

	/* The function without name is the default function that is called whenever anyone sends funds to a contract */
	function () payable {
		if (crowdsaleClosed) {
			throw;
		}
		uint totalAmount = msg.value;
		uint beneficiaryAmount = totalAmount * (1 - insurancePercent / 100);
		uint insurerAmount = totalAmount * insurancePercent / 100;
		balanceOf[msg.sender] = beneficiaryAmount;
		amountRaised += beneficiaryAmount;
		tokenReward.transfer(msg.sender, totalAmount / price);

		// Here is where the magic happens.
		// ICO sends part of invested money to its linked insurance contact.
		// This implies generation of some ammount of insurance tokens for every issues ICO token.
		//insurerAddr.transfer(insurerAmount);

		FundTransfer(msg.sender, totalAmount, true);
	}

	modifier afterDeadline() {
		if (now >= deadline) {
			_;
		}
	}

	/* checks if the goal or time limit has been reached and ends the campaign */
	function checkGoalReached() afterDeadline {
		if (amountRaised >= fundingGoal){
			fundingGoalReached = true;
			GoalReached(beneficiary, amountRaised);
		}
		crowdsaleClosed = true;
	}

	function safeWithdrawal() afterDeadline {
		if (!fundingGoalReached) {
			uint amount = balanceOf[msg.sender];
			balanceOf[msg.sender] = 0;
			if (amount > 0) {
				if (msg.sender.send(amount)) {
					FundTransfer(msg.sender, amount, false);
				}
				else {
					balanceOf[msg.sender] = amount;
				}
			}
		}

		if (fundingGoalReached && beneficiary == msg.sender) {
			if (beneficiary.send(amountRaised)) {
				FundTransfer(beneficiary, amountRaised, false);
			}
			else {
				//If we fail to send the funds to beneficiary, unlock funders balance
				fundingGoalReached = false;
			}
		}
	}
}
