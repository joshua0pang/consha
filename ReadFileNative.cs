using System;
using System.IO;

public partial class @FileSystem {

    public static void ReadCmdLine(out char[] result) {
        String[] arguments = Environment.GetCommandLineArgs();
        if (arguments.Length <= 1) {
            result = Console.In.ReadToEnd().ToCharArray();
        } else {
            result = File.ReadAllText(arguments[1]).ToCharArray();
        }
    }
}
