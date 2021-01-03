const spawn = require('child_process').spawn;
const child = spawn("./src/_build/default/main.exe", ["./test/busybox/tls_fe.c"]);


async function main(){
    child.stdin.setEncoding('utf-8');

    child.stdin.write("rnt\n");
    child.stdin.write("parents fe_select\n");
    child.stdout.on('data', function(data) {
        // There is some data to read now.
        console.log("" + data);

    });
    // child.stderr.on('data', function(data) {
    //     // There is some data to read now.
    //     console.error("" + data);

    // });
    await new Promise(resolve => setTimeout(resolve, 1000));
    // child.stdin.write("rnt\n");
    // child.stdin.write("nonfuns\n");

    child.stdin.end();
}

main()
