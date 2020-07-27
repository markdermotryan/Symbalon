# Symbalon

Python program for generating ProVerif scripts for verifying the
authentication properties of Symbalon. For details of the protocol,
see our paper:

"Symbalon: Privacy-preserving and Flexible Multi-device-based User Authentication".


Usage:

generate.py takes a 4-tuple of parameters  (n,n',t,t'), for example (5,2,3,1).

n = number of devices
n' = number of those that are "consentful"
t = threshold number required for authentication
t' = number of those required to be consentful (usually 1)

Examples
   python3 generate_model.py --params "(5,2,3,1)" --outfile symbolon_5_2_3_1.pv
      Generate a model for the given params. The outfile is optional.

   python3 generate_model.py --all_params 
      Generate many models, one for each of the sensible parameter values

ProVerif takes one of those output files and verifies the properties
(which are contained in the file).

Example
   proverif symbolon_5_2_3_1.pv
   
