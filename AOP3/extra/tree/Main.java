public class Main {
    public static void main(String[] args) {
        TreeNode<Integer> root = new TreeNode<>(0);
        {
            TreeNode<Integer> node1 = root.addChild(1);
            TreeNode<Integer> node2 = root.addChild(2);
            root.addChild(3);
            {
                node1.addChild(4);
                node1.addChild(5);
                TreeNode<Integer> node21 = node2.addChild(6);
                {
                    node21.addChild(7);
                }
            }
        }

        System.out.println(root.preorder());  // [0, 1, 4, 5, 2, 6, 7, 3]
        System.out.println(root.postorder()); // [4, 5, 1, 7, 6, 2, 3, 0]
        System.out.println(root.toString());
    }
}

//         0
//     /   |   \
//    1    2    3
//   / \   |
//  4   5  6
//         |
//         7
//
// preorder  -> [0, 1, 4, 5, 2, 6, 7, 3]
// postorder -> [4, 5, 1, 7, 6, 2, 3, 0]
