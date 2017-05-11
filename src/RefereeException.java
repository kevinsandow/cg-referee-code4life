public class RefereeException extends Exception {

    public RefereeException(String message, String source) {
        super(message + " : " + source);
    }

}
