'use-strict';
const util = require('util');
const spawn = require('child_process').spawn;

import Mutex from './mutex'
import { readFileSync, writeFileSync, fstat } from 'fs';

const exec_glob = util.promisify(require('child_process').exec);

const WORKDIR: string = "_____WORKDIR"

const BASE_ASSERT_DEF_UA = "int assert(int a) { if(a == 0){__VERIFIER_error();}\n "
const BASE_ASSERT_DEF_CBMC = "int assert(int a) { __CPROVER_ASSERT(\"postcondition\", a);}\n "
const BASE_ASSUME_DEF_UA = "int assume(int a) { if(a == 0){exit();}\n "
const BASE_ASSUME_DEF_CBMC = "int assume(int a) {__CPROVER_assume(a);}\n "

const exec_wd = (cmd: string) => exec_glob(`cd ${WORKDIR} && ${cmd}`)


const createWorkdir = async () => await exec_glob(`mkdir ${WORKDIR}`)
const cleanUp = async () => {
    try {
        await exec_glob(`rm -rf ${WORKDIR}`)
    } catch{ }
}

interface ProgramAttributes {
    allFuns: string[]
    parents: FunctionMappings
    assertFuns: string[]
    funcLocations: FunctionMappings
}


const addDefsToFile = async (file: string, verifier: string) => {
  
    writeFileSync(`${WORKDIR}/${file}`, readFileSync(`${WORKDIR}/${file}`).toString())
 
    if(verifier === "ua"){
        writeFileSync(`${WORKDIR}/${file}`, BASE_ASSERT_DEF_UA + BASE_ASSUME_DEF_UA + readFileSync(`${WORKDIR}/${file}`).toString() )
    }else{
        writeFileSync(`${WORKDIR}/${file}`, BASE_ASSERT_DEF_CBMC + BASE_ASSUME_DEF_CBMC + readFileSync(`${WORKDIR}/${file}`).toString())

    }

}

type FunctionMappings = Record<string, string>

enum ProofStatus {
    success,
    fail,
    unattempted
}

interface LatticeNode {
    function: string
    proofLocal: ProofStatus
    proofActual: ProofStatus
    mutex: Mutex
    provenParent: LatticeNode | null
}


type Status = Record<string, LatticeNode>

interface Result {
    loc: string
    provedAt: string | null
    isTrue: boolean
}

function waitForEventWithTimeout(socket, event, t) : Promise<string> {
    return new Promise(function(resolve, reject) {
        let timer : NodeJS.Timeout;

        function listener(data) {
            clearTimeout(timer);
            socket.removeListener(event, listener);
            resolve("" + data);
        }

        socket.on(event, listener);
        timer = setTimeout(function() {
            socket.removeListener(event, listener);
            reject(new Error("timeout"));
        }, t);
    });
}




const verify = async (filename, verifier : string, sync: boolean) => {
    let buffer: string = "";
    const child = spawn("./src/_build/default/main.exe", [filename]);
    child.stdin.setEncoding('utf-8');


    console.log(filename)
    async function runCommand(command: string){
        child.stdin.write(command + '\n')
        while(true){
            const chunk = await waitForEventWithTimeout(child.stdout, 'data', 5000);
            buffer += chunk
            if (buffer.includes("$SICC_SERVER_DONE")){
                const out = buffer.split("$SICC_SERVER_DONE")
                buffer = out.slice(1).join("")
                return out[0]
            }
        }
    }
    

    const status : Status = {} 

    function getNode(fun: string) : LatticeNode {
        if (status[fun]){
            return status[fun]
        }else{
            status[fun] = {
                function: fun,
                proofLocal: ProofStatus.unattempted,
                proofActual: ProofStatus.unattempted,
                mutex: new Mutex(),
                provenParent: null,
            } as LatticeNode
            return status[fun]
        }
    }

    async function getParents(fun: string): Promise<Array<string>> {
        const response = await runCommand(`parents ${fun}`);
        return response.split("\n").map((s: string) => s.trim()).filter(s => s != "");
    }

    const assertFuns = await getParents("assert");


    const prove = async (fun: LatticeNode, previous: LatticeNode | null): Promise<void> => {
   
        await fun.mutex.lock()
        
        switch (fun.proofActual) {
            case ProofStatus.unattempted: {
                try {
                    const targetfile = `${fun.function}.c`;
                    const code = await runCommand(`print ${fun.function}`)
                    writeFileSync(`${WORKDIR}/${targetfile}`, code)
                    addDefsToFile(targetfile, verifier)

                    console.log(fun.function)
                    if(verifier == "cbmc"){
                        await exec_wd(`cbmc ${targetfile} --unwinding-assertions --unwind 201 --function ${fun.function} > /dev/null`)
                    }else if(verifier == "ua"){
                        // throw Error;
                        // targetfile = "output.c"

                        const pwd = await exec_wd(`pwd`)
                            .then((r: any) => r.stdout.trim())
                            .catch((err: any) => console.log(err))
                        
                        await exec_wd(`mkdir ${fun.function}`)
                        writeFileSync(`${pwd}/${fun.function}/PropertyUnreachCall.prp`, `CHECK( init(${fun.function}()), LTL(G ! call(__VERIFIER_error())) )`);
                        const ua = await exec_glob(`cd ~/uauto && ./Ultimate.py --spec ${pwd}/${fun.function}/PropertyUnreachCall.prp --architecture 64bit --file ${pwd}/${targetfile} | grep -E -- 'TRUE|FALSE'`,)

                        console.log(fun.function + ua.stdout)
                        if(!ua.stdout.includes("TRUE")){
                            throw Error;
                        }
                    }
                    fun.proofActual = ProofStatus.success
                    fun.proofLocal = ProofStatus.success
                    fun.provenParent = fun
                } catch(e) {
                    fun.proofLocal = ProofStatus.fail
                    const parents = await getParents(fun.function);
                    if (parents.length > 0) {
                        await Promise.all(parents.map(p => prove(getNode(p as string), fun)))
                    }
                    else {
                        fun.proofLocal = ProofStatus.fail
                    }
                }
                // fall through 
            }
            case ProofStatus.success:
            case ProofStatus.fail: {
                if (previous) {
                    previous.provenParent = fun.provenParent
                    previous.proofActual = fun.proofActual
                }
            }
        }
       
        fun.mutex.release();
        
    }

    if(sync){
        for (const fun of assertFuns) {
            await prove(getNode(fun), null);
        }
    }
    else{
        await Promise.all(assertFuns.map((fun: string) => prove(getNode(fun), null)))
    }

    return assertFuns.map((fun: string) => {
        const getLOC = (fun: string) => {
            return  fun
        }


        return {
                loc: getLOC(fun),
                isTrue: status[fun].proofActual === ProofStatus.success,
                provedAt: status[fun].provenParent ? getLOC(status[fun].provenParent!.function) : null,
                // solveTime: 0
            } as Result
    
    });
}

module.exports = {
    createWorkdir,
    cleanUp,
    verify,
}