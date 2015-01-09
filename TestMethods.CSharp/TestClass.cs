using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace TestMethods.CSharp
{

    public class TestClass
    {
        public static int Test0(int a, int b)
        {
            return a + b;
        }

        public static int Test1(int a)
        {
            var sum = a;
            while (sum < 100)
            {
                sum += a;
            }

            return a;
        }

        public static int Test2(int a)
        {
            var sum = a;
            for (int i = 0; i < a; i++)
                sum += a * i;

            return a;
        }

        public static int Test3(int a)
        {
            switch (a)
            {
                case 0:
                case 1:
                    return a;
                case 10:
                    return a / 10;
                default:
                    return 0;
            }
        }

        public static int Test4(int a, int b)
        {
            var bound = Math.Min(a, b);
            if (bound > 0)
            {
                if (bound + b >= 13)
                    return b;
                else
                    return bound * bound;
            }
            else if (a < 0)
                return a;
            else
            {
                if (b % 2 == 0) return b / 2;
                else return a + 7;
            }
        }


        public static int Test5(List<int> l)
        {
            var sum = 0;
            foreach (var a in l)
            {
                sum += a;
            }

            return sum;
        }

        public static Tuple<int, int> Test6(int a, int b)
        {
            int d = 0;
            int c = a * b;
            Action<int, int> add = (ai, bi) => d = ai + bi + c;

            Func<int, int, Tuple<int, int>> tup = (x, y) => new Tuple<int, int>(x, y);

            add(a, b);
            return tup(d, d);
        }

    }
}
