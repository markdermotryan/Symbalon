#!/usr/bin/python3

"""
Generate ProVerif model for Symbolon authentication system

It takes a 4-tuple of parameters  (n,n',t,t'), for example (5,2,3,1).

n = number of devices
n' = number of those that are "consentful"
t = threshold number required for authentication
t' = number of those required to be consentful (usually 1)

Examples
   python3 generate_model.py --params "(5,2,3,1)" --outfile symbolon_5_2_3_1.pv
      Generate a model for the given params. The outfile is optional.

   python3 generate_model.py --all_params 
      Generate many models, one for each of the sensible parameter values

"""

import argparse
import os
import itertools

def output_proverif(f, n, np, t, tp):
    """ Output to filehandler f the symbolon script parameterised by n, np, t, tp """
    def writeln(x):
        f.write(x + "\n")
    def write(x):
        f.write(x)

    writeln(f"")
    writeln(f"")
    writeln(f"(*")
    writeln(f"ProVerif script to verify authentication properties of Symbolon")
    writeln(f"")
    writeln(f"For a description of the protocol, see our paper")
    writeln(f"Symbolon: Privacy-preserving and Flexible Multi-device-based User Authentication")
    writeln(f"*)")
    writeln(f"")
    writeln(f"")
    writeln(f"(* public channel *)")
    writeln(f"free c: channel.")
    writeln(f"")
    writeln(f"(* private channels for sending secrets from the dealer to the n and the n' of them that are consentful authenticators *)")

    for i in range(n):
        writeln(f"free pc{i}: channel [private].")
    for i in range(np):
        writeln(f"free pcc{i}: channel [private].")

    writeln(f"")
    writeln(f"(* channel for communicating the public key to the relying party *)")
    writeln(f"free pcRP: channel [private].")
    writeln(f"")
    writeln(f"(* some free names available to the attacker *)")
    for i in range(n):
        writeln(f"free name{i}: bitstring.")
    for i in range(np):
        writeln(f"free name_c{i}: bitstring.")

    writeln(f"")
    writeln(f"event authorised(bitstring). (* the bitstring challenge has been authorised, i.e. signed by the required cohort of signers *)")
    writeln(f"event signed(channel, bitstring). (* the bitstring challenge has been signed by a regular signer denoted by the private channel pc *)")
    writeln(f"event csigned(channel, bitstring). (* the bitstring challenge has been signed by a consentful signer denoted by the private channel pc *)")
    writeln(f"")
    writeln(f"(*")
    writeln(f"There are {n} regular key shares.")
    writeln(f"There are {np} 'consentful' key shares.")
    writeln(f"A valid signature is made using:")
    writeln(f"- {t} of the {n} key regular shares, and also")
    writeln(f"- {tp} of the {np} consent key shares")
    writeln(f"*)")
    writeln(f"")
    writeln(f"type secretkey. (* secret key for authentication *)")
    writeln(f"type publickey. (* public key corresponding to secret key *)")
    writeln(f"type kshare.        (* share of secret key *)")
    writeln(f"type ckshare.        (* consentful share of secret key *)")
    writeln(f"")
    writeln(f"fun pk(secretkey):publickey.  (* derive public key from a secret key *)")

    for i in range(n):
        writeln(f"fun ksh{i}(secretkey): kshare.  (* derive the key shares from the secret key *)")
    for i in range(np):
        writeln(f"fun cksh{i}(secretkey): ckshare.  (* derive the consentful key shares from the secret key *)")

    writeln(f"")
    writeln(f"")
    writeln(f"(* combine is the function that makes a single signature out of partial signatures *)")
    writeln(f"(* combine has arity {t + tp} *)")
    writeln(f"fun combine({'bitstring, '*(t + tp - 1)} bitstring): bitstring.")
    writeln(f"")
    writeln(f"(* sign with a key share, and with a consentful key share *)")
    writeln(f"fun sign(kshare, bitstring): bitstring.")
    writeln(f"fun csign(ckshare,bitstring): bitstring.")
    writeln(f"")
    writeln(f"(* a valid combination of signatures made with shares can be verified.")
    writeln(f"'Valid' means {tp} consentful signature(s) and {t} ordinary ones *)")

    reduc_clause = "reduc\n"
    for signer_tuple in itertools.combinations(range(n), t):
        for c_signer_tuple in itertools.combinations(range(np), tp):
            reduc_clause += "forall sk:secretkey, m:bitstring;  verify(pk(sk), m, combine("
            for i in signer_tuple:
                reduc_clause += f" sign(ksh{i}(sk),m),"
            for i in c_signer_tuple:
                reduc_clause += f" csign(cksh{i}(sk),m),"
            assert(reduc_clause[-1] == ",")
            reduc_clause = reduc_clause[:-1] # delete the last comma
            reduc_clause += f") ) = true;\n"
    assert(reduc_clause[-2] == ";")
    reduc_clause = reduc_clause[:-2] + ".\n" # replace ";\n" with ".\n"
    writeln(reduc_clause)

    writeln(f"")
    writeln(f"")
    writeln(f"(* Properties to be checked")
    writeln(f"=========================== *)")
    writeln(f"")
    writeln(f"(* If an access has been authorised, then some {t} of the {n} regular signers must have signed it *)")
    writeln(f"")

    query_clause = f"query chal:bitstring; event(authorised(chal)) ==> (\n"
    for signer_tuple in itertools.combinations(range(n), t):
            query_clause += " ("
            for i in signer_tuple:
                query_clause += f" event(signed(pc{i}, chal)) &&"
            assert(query_clause[-2:] == "&&")
            query_clause = query_clause[:-2] + ") ||\n" 
    assert(query_clause[-3:] == "||\n")
    query_clause = query_clause[:-3] + ").\n"
    writeln(query_clause)

    
    writeln(f"(* If an access has been authorised, then {tp} of the {np} consentful signers must have signed it *)")
    writeln(f"")

    query_clause = f"query chal:bitstring; event(authorised(chal)) ==> (\n"
    for c_signer_tuple in itertools.combinations(range(np), tp):
            query_clause += " ("
            for i in c_signer_tuple:
                query_clause += f" event(csigned(pcc{i}, chal)) &&"
            assert(query_clause[-2:] == "&&")
            query_clause = query_clause[:-2] + ") ||\n" 
    assert(query_clause[-3:] == "||\n")
    query_clause = query_clause[:-3] + ").\n"
    writeln(query_clause)

    writeln(f"(* Reachability check *)")
    writeln(f"query chal:bitstring; event(authorised(chal)).")
    writeln(f"")
    writeln(f"")
    writeln(f"(* Definition of the protocol participants *)")
    writeln(f"")
    writeln(f"let Dealer =")
    writeln(f"     new sk: secretkey;")
    writeln(f"     out(c, pk(sk));")
    writeln(f"     (* out(c, ksh1(sk)); *)")
    writeln(f"     (* uncomment line above to see an attack *)")
    writeln(f"     (  out(pcRP, pk(sk)) |")
    writeln(f"        (* let the attacker control whether a signer is enabled or not *)")


    for i in range(n):
        writeln(f"        ( in(c, =name{i}  ); out(pc{i}, ksh{i}(sk))  )|")
    for i in range(np):
        writeln(f"        ( in(c, =name_c{i}); out(pcc{i}, cksh{i}(sk)) )|")
    writeln(f"        0 ).")
    writeln(f"")
    writeln(f"(* a regular signer has a regular key share *)")
    writeln(f"let Signer(pc: channel) =")
    writeln(f"     in(pc, k:kshare );")
    writeln(f"     in(c, mess:bitstring);")
    writeln(f"     let s = sign(k, mess) in")
    writeln(f"     event signed(pc, mess);")
    writeln(f"     out(c, s).")
    writeln(f"")
    writeln(f"(* a consentful signer has both a regular key share and a consentful key share *)")
    writeln(f"let ConsentfulSigner(pc: channel, pcc:channel) =")
    writeln(f"     in(pc, k:kshare);")
    writeln(f"     in(pcc, kc:ckshare);")
    writeln(f"     in(c, mess:bitstring);")
    writeln(f"     let s = sign(k, mess) in")
    writeln(f"     let sc = csign(kc, mess) in")
    writeln(f"     event signed(pc, mess);")
    writeln(f"     event csigned(pcc, mess);")
    writeln(f"     out(c, s);")
    writeln(f"     out(c, sc).")
    writeln(f"")
    writeln(f"")
    writeln(f"let RelyingParty =")
    writeln(f"     in(pcRP, pubkey:publickey);")
    writeln(f"     new challenge: bitstring;")
    writeln(f"     out(c, challenge);")
    writeln(f"     in(c, s:bitstring);")
    writeln(f"     if verify(pubkey, challenge, s) = true then")
    writeln(f"     event authorised(challenge).")
    writeln(f"  ")
    writeln(f"")
    writeln(f"process")
    writeln(f"     (!Dealer) | (!RelyingParty) | ")
    writeln(f"     (* There are {np} consentful signers, and {n - np} ordinary signers *) ")
    for i in range(n):
        if i < np:
            writeln(f"     (!ConsentfulSigner(pc{i}, pcc{i})) | ")
        else:
            writeln(f"     (!Signer(pc{i})) | ")                    
    writeln(f"     0")
    writeln(f"")
    return
    
if __name__=="__main__":
    parser = argparse.ArgumentParser(
        description = "Generate symbolon model",
        epilog = "python3 generate_model.py --params '(5,2,3,1)' --outfile symbolon_5_2_3_1.pv")
    parser.add_argument('--params', help="4-tuple of parameters, for example (5,2,3,1). Probably needs quotes to escape processing by your command shell")
    parser.add_argument('--outputfile', help="Output file", default=None)
    parser.add_argument('--all_params', action='store_true', help="Output many models, one for all the sensible param values")
    prog_args = parser.parse_args()

    if prog_args.params != None:
        (n,np,t,tp) = eval(prog_args.params)
        if prog_args.outputfile == None:
            prog_args.outputfile = "symbolon_" + "_".join((str(n), str(np), str(t), str(tp))) + ".pv"
        with open(prog_args.outputfile, 'w') as f:    
            output_proverif(f,n,np,t,tp)

    elif prog_args.all_params:
        with open("run_proverif", 'w') as f:
            pass
        # n_ran = range(1,6) # range for "n". Modify this one to control which files are generated.
        # n_ran = range(6,7) 
        n_ran = range(7,8)
        # n_ran = range(8,9) # impossible
        ran = range(1,9)   # range for other params. No need to modify this.
        for n in n_ran:
            for np in ran:
                for t in ran:
                    for tp in ran:
                        if not (n >= np and t >= tp and n > t and np >= tp): continue
                        print(f"Generating model for ({n},{np},{t},{tp})")
                        param_string = "_".join((str(n), str(np), str(t), str(tp)))
                        outputfile = "symbolon_" + param_string + ".pv"
                        with open(outputfile, 'w') as f:    
                            output_proverif(f,n,np,t,tp)
                        # output a line in run_proverif (a bash script)
                        with open("run_proverif", 'a') as f:
                            f.write(f"proverif {outputfile} | tee output/out_{param_string}\n")
        # grep RESULT out* | sed -e "s/^\(............................\).*\(......\)/\1 \2/"

    else:
        print("Bad command-line options. Don't know what to do.")
        
    exit()
    
        
    
