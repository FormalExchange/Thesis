#Introduction.

This folder contains the coq formalization of double-sided auctions with multiplicity (dsam). 
DSA is used in the financial markets by exchanges for trading between multiple buyers with multiple sellers. 
For example,  double-sided auction with multiplicity is used during the call auction session of trading at a stock exchange. 
In this formalization, we have modeled and formalized various properties of double sided auction along with their algorithms. 
We extract a certified OCaml, Haskell programs for matching buyers with seller at the stock exchange during call auction session.
We also have demonstrated our extracted OCaml programs on real market data. Please see directory Demonstration.

#How to use the coq formalization: To compile the code please run the executable shell script auction.sh

# Coq files details: We have formalized matching at the financial exchanges. 
0. All the important results, processes and programs are extracted in Demo.v file. To run this file, please 
run auction.sh file from you terminal ($ ./auction.sh). This file may take 5-6 minutes to compile. 
Once auctions.sh is successfully completed, please run "coqc Demo.v" from your terminal. In short, 
type the following command from your terminal:

> ./auction.sh;
> coqc Demo.v 

1. The main lemmas for the correctness of fairness are in the file FAIR.v
2. The UM process and its correctness theorems are in UM.v. The UM process is used at the exchanges.
3. For MM process, go to the file MM.v.
4. The Bound.v file contains combinatorial results on matchings. 
5. The Uniqueness.v file contains uniqueness related results.

