const spawn = require('child_process').spawn;
const child = spawn("./src/_build/default/main.exe", ["./test/busybox/tls_fe.c"]);




function waitForEventWithTimeout(socket, event, t) {
    return new Promise(function(resolve, reject) {
        let timer 

        function listener(data) {
            console.log(data)
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
let buffer= ""
async function getResponse(){
    while(true){
        const chunk = await waitForEventWithTimeout(child.stdout, 'data', 4000);
        buffer += chunk
        if (buffer.includes("$SICC_SERVER_DONE")){
            const out = buffer.split("$SICC_SERVER_DONE")
            buffer = out.slice(1).join("")
            return out[0]
        }
    }
}

async function main(){


    child.stdin.setEncoding('utf-8');
    child.on('close', () => {console.log("fyck")})

    // child.stdin.write("rnt\n");
    // child.stdin.write("print __old_main\n");
    // console.log(await getResponse())
    
    // let response = await getResponse();
    // console.log(response)


    child.stdin.write("print RNT_NODE_0\n");
    response = await getResponse();
    console.log(response)

    child.stdin.write("parents RNT_NODE_0\n");
    response = await getResponse();
    console.log(response)
    // await getResponse();
    // getResponse();
    // child.stdin.write("print __old_main\n");
    // await getResponse();
    // child.stdin.write("parents fe_select\n");

    // child.stderr.on('data', function(data) {
    //     // There is some data to read now.
    //     console.error("" + data);

    // });
    // await new Promise(resolve => setTimeout(resolve, 1000));
    // child.stdin.write("rnt\n");
    // child.stdin.write("nonfuns\n");

    child.stdin.end();
}

main()
