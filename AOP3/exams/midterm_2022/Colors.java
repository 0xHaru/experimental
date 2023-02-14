public enum Colors {
    Green, Yellow, Red;

    public static Colors next(Colors c) {
        int pos = c.ordinal();
        return Colors.values()[++pos % 3];
    }
}
